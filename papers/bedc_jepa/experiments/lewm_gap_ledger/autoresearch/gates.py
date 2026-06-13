#!/usr/bin/env python3
"""Deterministic LeWM acceptance gates for experiment verdicts."""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from copy import deepcopy
from pathlib import Path
from typing import Any

try:
    from schemas import validate_all
    from store import LeWMPaths, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from schemas import validate_all
    from store import LeWMPaths, read_jsonl, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
TOLERANCE = 1e-9


def _get_path(record: dict[str, Any], dotted: str) -> Any:
    current: Any = record
    for part in dotted.split("."):
        if not isinstance(current, dict) or part not in current:
            return None
        current = current[part]
    return current


def _strip_wall_time(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: _strip_wall_time(item) for key, item in value.items() if key != "wall_time"}
    if isinstance(value, list):
        return [_strip_wall_time(item) for item in value]
    return value


def gate_anchor(verdict: dict[str, Any], contact: dict[str, Any], *, tolerance: float = TOLERANCE) -> dict[str, Any]:
    reasons: list[str] = []
    frozen = contact.get("frozen_fields") if isinstance(contact.get("frozen_fields"), dict) else {}
    for field, expected in frozen.items():
        observed = _get_path(verdict, str(field))
        if observed is None and isinstance(verdict.get("metrics"), dict):
            observed = verdict["metrics"].get(str(field))
        if not isinstance(expected, (int, float)) or not isinstance(observed, (int, float)):
            reasons.append(f"{field}: expected and observed values must both be numeric")
            continue
        if abs(float(observed) - float(expected)) > tolerance:
            reasons.append(f"{field}: observed={observed} expected={expected} tolerance={tolerance}")
    return {"gate": "anchor", "passed": not reasons, "reasons": reasons}


def gate_reproducibility(verdict: dict[str, Any], all_verdicts: list[dict[str, Any]]) -> dict[str, Any]:
    group = str(verdict.get("replicate_group") or "")
    comparable = [
        item
        for item in all_verdicts
        if str(item.get("replicate_group") or "") == group and str(item.get("verdict_id") or "") != str(verdict.get("verdict_id") or "")
    ]
    if not comparable:
        return {"gate": "reproducibility", "passed": False, "reasons": [f"replicate_group {group} has fewer than two runs"]}
    stripped = _strip_wall_time({key: value for key, value in verdict.items() if key != "verdict_id"})
    reasons: list[str] = []
    for other in comparable:
        other_stripped = _strip_wall_time({key: value for key, value in other.items() if key != "verdict_id"})
        if other_stripped == stripped:
            return {"gate": "reproducibility", "passed": True, "reasons": []}
        reasons.append(f"replicate {other.get('verdict_id')} differs after stripping wall_time")
    return {"gate": "reproducibility", "passed": False, "reasons": reasons}


def _claim_from_ci(experiment: dict[str, Any], verdict: dict[str, Any]) -> tuple[str, str]:
    criterion = experiment.get("criterion") if isinstance(experiment.get("criterion"), dict) else {}
    kind = str(criterion.get("kind") or "")
    metric = str(criterion.get("metric") or "")
    ci = verdict.get("ci") if isinstance(verdict.get("ci"), dict) else {}
    bounds = ci.get(metric) if isinstance(ci.get(metric), dict) else {}
    low = bounds.get("low")
    high = bounds.get("high")
    if not isinstance(low, (int, float)) or not isinstance(high, (int, float)):
        return "unidentifiable", f"{metric}: CI must contain numeric low/high"
    if low > high:
        return "unidentifiable", f"{metric}: CI low exceeds high"
    if kind in {"delta_ci_below_zero", "uer_ci_separation"}:
        if high < 0:
            return "positive", f"{metric}: CI high < 0"
        if low >= 0:
            return "negative", f"{metric}: CI low >= 0"
        return "unidentifiable", f"{metric}: CI crosses 0"
    if kind == "delta_ci_above_zero":
        if low > 0:
            return "positive", f"{metric}: CI low > 0"
        if high <= 0:
            return "negative", f"{metric}: CI high <= 0"
        return "unidentifiable", f"{metric}: CI crosses 0"
    if kind == "auroc_ci_separation":
        threshold = float(criterion.get("null", 0.5))
        if low > threshold:
            return "positive", f"{metric}: CI low > {threshold}"
        if high <= threshold:
            return "negative", f"{metric}: CI high <= {threshold}"
        return "unidentifiable", f"{metric}: CI crosses {threshold}"
    if kind == "manual":
        return str(verdict.get("status") or "unidentifiable"), "manual criterion"
    return "unidentifiable", f"unsupported criterion kind: {kind}"


def gate_criterion(verdict: dict[str, Any], experiment: dict[str, Any]) -> dict[str, Any]:
    inferred, reason = _claim_from_ci(experiment, verdict)
    reported = str(verdict.get("status") or "")
    if reported == "fail-closed":
        return {"gate": "criterion", "passed": True, "reasons": ["fail-closed verdict bypasses positive/negative CI claim"]}
    passed = inferred == reported
    return {
        "gate": "criterion",
        "passed": passed,
        "reasons": [] if passed else [f"reported status {reported} disagrees with CI-inferred {inferred}: {reason}"],
        "inferred_status": inferred,
    }


def gate_overclaim(verdict: dict[str, Any], contact: dict[str, Any]) -> dict[str, Any]:
    can_measure = {str(item) for item in contact.get("can_measure", []) if isinstance(item, str)}
    measured = {str(item) for item in verdict.get("measured_scope", []) if isinstance(item, str)}
    cannot_measure = {str(item) for item in contact.get("cannot_measure", []) if isinstance(item, str)}
    reasons: list[str] = []
    outside = sorted(measured - can_measure)
    forbidden = sorted(measured & cannot_measure)
    if outside:
        reasons.append(f"measured_scope outside contact can_measure: {outside}")
    if forbidden:
        reasons.append(f"measured_scope enters contact cannot_measure: {forbidden}")
    claim = str(verdict.get("reported_claim") or "")
    for forbidden_scope in sorted(cannot_measure):
        if forbidden_scope and forbidden_scope in claim:
            reasons.append(f"reported_claim mentions unmeasurable scope: {forbidden_scope}")
    return {"gate": "overclaim", "passed": not reasons, "reasons": reasons}


def gate_provenance(verdict: dict[str, Any]) -> dict[str, Any]:
    provenance = str(verdict.get("provenance") or "")
    if provenance == "executed":
        return {"gate": "gate_provenance", "passed": True, "reasons": []}
    return {"gate": "gate_provenance", "passed": False, "reasons": [f"verdict provenance is not executed: {provenance or 'missing'}"]}


def gate_verdict(
    verdict: dict[str, Any],
    *,
    experiments_by_id: dict[str, dict[str, Any]],
    contacts_by_id: dict[str, dict[str, Any]],
    all_verdicts: list[dict[str, Any]],
) -> dict[str, Any]:
    experiment = experiments_by_id.get(str(verdict.get("experiment_ref") or ""))
    contact = contacts_by_id.get(str(verdict.get("contact_ref") or ""))
    gate_results: list[dict[str, Any]] = []
    if experiment is None:
        gate_results.append({"gate": "experiment_ref", "passed": False, "reasons": [f"experiment not found: {verdict.get('experiment_ref')}"]})
    if contact is None:
        gate_results.append({"gate": "contact_ref", "passed": False, "reasons": [f"contact not found: {verdict.get('contact_ref')}"]})
    if experiment is not None and contact is not None:
        gate_results.extend(
            [
                gate_anchor(verdict, contact),
                gate_reproducibility(verdict, all_verdicts),
                gate_criterion(verdict, experiment),
                gate_overclaim(verdict, contact),
                gate_provenance(verdict),
            ]
        )
    passed = all(result.get("passed") is True for result in gate_results)
    return {
        "verdict_id": verdict.get("verdict_id"),
        "experiment_ref": verdict.get("experiment_ref"),
        "contact_ref": verdict.get("contact_ref"),
        "gate_status": "gate_passed" if passed else "gate_blocked",
        "gates": gate_results,
        "issues": [reason for result in gate_results for reason in result.get("reasons", [])],
    }


def gate_all(
    hypotheses: list[dict[str, Any]],
    experiments: list[dict[str, Any]],
    contacts: list[dict[str, Any]],
    verdicts: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    validation = validate_all(hypotheses, experiments, contacts, verdicts)
    validation_issues = {
        str(row["id"]): row["issues"]
        for rows in validation.values()
        for row in rows
        if row["issues"]
    }
    experiments_by_id = {str(item.get("experiment_id")): item for item in experiments}
    contacts_by_id = {str(item.get("contact_id")): item for item in contacts}
    results: list[dict[str, Any]] = []
    for verdict in verdicts:
        verdict_id = str(verdict.get("verdict_id") or "")
        if verdict_id in validation_issues:
            issues = validation_issues[verdict_id]
            results.append(
                {
                    "verdict_id": verdict.get("verdict_id"),
                    "experiment_ref": verdict.get("experiment_ref"),
                    "contact_ref": verdict.get("contact_ref"),
                    "gate_status": "gate_blocked",
                    "gates": [{"gate": "schema", "passed": False, "reasons": issues}],
                    "issues": issues,
                }
            )
            continue
        results.append(gate_verdict(verdict, experiments_by_id=experiments_by_id, contacts_by_id=contacts_by_id, all_verdicts=verdicts))
    return results


def _fixture_packets() -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    hypothesis = {
        "hypothesis_id": "fi-001.cvar-tail",
        "predicate": "CVaR tail objective makes allocation_delta negative.",
        "failure_surface": "allocation delta CI",
        "horizon": {"steps": [1, 4, 8]},
        "perturbation_family": "tail-risk weighting",
        "carrier": "pusht checkpoint export",
        "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
        "reality_contact_refs": ["pusht.phase2c.export"],
        "status": "open",
    }
    experiment = {
        "experiment_id": "exp.fi-001.cvar-tail",
        "hypothesis_ref": "fi-001.cvar-tail",
        "script_name": "_phase2c_ood_aware_gap.py",
        "input_data": ["pusht_latent_large.npz"],
        "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
        "predeclared_thresholds": {"alpha": 0.05},
        "required_contacts": ["pusht.phase2c.export"],
        "status": "planned",
    }
    contact = {
        "contact_id": "pusht.phase2c.export",
        "source_kind": "checkpoint-export",
        "checkpoint": "pusht_latent_large.npz",
        "export_ref": "_phase2c_full_run.log",
        "can_measure": ["allocation_delta", "uer", "auroc"],
        "cannot_measure": ["real_robot_transfer"],
        "frozen_fields": {"anchor.metric": 0.123456789},
        "notes": "self-test contact",
    }
    base_verdict = {
        "verdict_id": "verdict.fi-001.cvar-tail.a",
        "experiment_ref": "exp.fi-001.cvar-tail",
        "contact_ref": "pusht.phase2c.export",
        "status": "positive",
        "reported_claim": "allocation_delta < 0 on exported pusht latents",
        "provenance": "executed",
        "acceptance": {"status": "pending"},
        "metrics": {"anchor.metric": 0.123456789, "allocation_delta": -0.02},
        "ci": {"allocation_delta": {"low": -0.04, "high": -0.01}},
        "anchoring": {"anchor.metric": 0.123456789},
        "replicate_group": "rg.fi-001.pass",
        "run_fingerprint": "sha256.fixture.pass",
        "measured_scope": ["allocation_delta"],
        "wall_time": 1.25,
    }
    replicate = deepcopy(base_verdict)
    replicate["verdict_id"] = "verdict.fi-001.cvar-tail.b"
    replicate["wall_time"] = 1.99
    bad = deepcopy(base_verdict)
    bad.update(
        {
            "verdict_id": "verdict.fi-001.overclaim",
            "reported_claim": "allocation_delta < 0 and real_robot_transfer improves",
            "replicate_group": "rg.fi-001.fail",
            "measured_scope": ["allocation_delta", "real_robot_transfer"],
        }
    )
    bad_rep = deepcopy(bad)
    bad_rep["verdict_id"] = "verdict.fi-001.overclaim.rep"
    stub = deepcopy(base_verdict)
    stub.update(
        {
            "verdict_id": "verdict.fi-001.stub",
            "reported_claim": "stub dry-run for allocation_delta; no scientific claim",
            "provenance": "stub",
            "status": "fail-closed",
            "ci": {"allocation_delta": {"low": -0.01, "high": 0.01}},
            "metrics": {"anchor.metric": 0.123456789, "allocation_delta": 0.0},
            "replicate_group": "rg.fi-001.stub",
            "run_fingerprint": "sha256.fixture.stub",
        }
    )
    stub_rep = deepcopy(stub)
    stub_rep["verdict_id"] = "verdict.fi-001.stub.rep"
    stub_rep["wall_time"] = 1.99
    return [hypothesis], [experiment], [contact], [base_verdict, replicate, bad, bad_rep, stub, stub_rep]


def self_test() -> int:
    hypotheses, experiments, contacts, verdicts = _fixture_packets()
    results = gate_all(hypotheses, experiments, contacts, verdicts)
    by_id = {str(item.get("verdict_id")): item for item in results}
    if by_id["verdict.fi-001.cvar-tail.a"]["gate_status"] != "gate_passed":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["verdict.fi-001.overclaim"]["gate_status"] != "gate_blocked":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["verdict.fi-001.stub"]["gate_status"] != "gate_blocked":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    provenance_gate_stub = next((gate for gate in by_id["verdict.fi-001.stub"]["gates"] if gate.get("gate") == "gate_provenance"), {})
    provenance_gate_executed = next((gate for gate in by_id["verdict.fi-001.cvar-tail.a"]["gates"] if gate.get("gate") == "gate_provenance"), {})
    if provenance_gate_stub.get("passed") is not False or provenance_gate_executed.get("passed") is not True:
        print(json.dumps({"stub": provenance_gate_stub, "executed": provenance_gate_executed}, indent=2), file=sys.stderr)
        return 1
    if not any("real_robot_transfer" in issue for issue in by_id["verdict.fi-001.overclaim"]["issues"]):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "gate_results.jsonl"
        write_jsonl(out, results)
        reread = read_jsonl(out)
        if len(reread) != len(results):
            print(str(out), file=sys.stderr)
            return 1
    print("[lewm-gates] self-test ok; gate_provenance stub=blocked executed=passed")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run LeWM verdict acceptance gates")
    parser.add_argument("--hypotheses", default=str(LeWMPaths.hypotheses))
    parser.add_argument("--experiments", default=str(LeWMPaths.experiments))
    parser.add_argument("--contacts", default=str(LeWMPaths.contacts))
    parser.add_argument("--verdicts", default=str(LeWMPaths.verdicts))
    parser.add_argument("--output", default=str(LeWMPaths.gate_results))
    parser.add_argument("--allow-empty", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    try:
        hypotheses = read_jsonl(Path(args.hypotheses))
        experiments = read_jsonl(Path(args.experiments))
        contacts = read_jsonl(Path(args.contacts))
        verdicts = read_jsonl(Path(args.verdicts))
        if not args.allow_empty and not verdicts:
            print("[lewm-gates] no verdicts", file=sys.stderr)
            return 1
        results = gate_all(hypotheses, experiments, contacts, verdicts)
        write_jsonl(Path(args.output), results)
    except Exception as exc:
        print(f"[lewm-gates] error: {exc}", file=sys.stderr)
        return 1
    blocked = sum(1 for result in results if result.get("gate_status") == "gate_blocked")
    passed = len(results) - blocked
    print(f"[lewm-gates] wrote {len(results)} result(s) to {args.output}; passed={passed} blocked={blocked}")
    return 0 if blocked == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
