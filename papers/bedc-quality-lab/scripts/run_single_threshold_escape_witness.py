#!/usr/bin/env python3
"""Produce a pointer-only sidecar for single-threshold escape witnessing."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.research_discovery import assign_discovery_level


LOCAL_SCHEMA_ID = "bedc-quality-lab:single-threshold-escape-witness-sidecar"
JSON_ARTIFACT = "runs/single_threshold_escape_witness.json"
MARKDOWN_ARTIFACT = "runs/single_threshold_escape_witness.md"
THRESHOLD_ARTIFACT = "reports/canonical/gap-head-threshold-frontier.json"
CANONICAL_ROLE = "sidecar-not-in-CANONICAL_REPORTS"
POSITIVE_RULE = "AUROC.ci95_low > 0.5"
ESCAPE_LEVELS = {"D4", "D5-O", "D5-M"}
FORBIDDEN_CLAIM_KEYS = {"score", "total_score", "rank", "grade", "hidden_cost", "hidden_cost_weight", "hidden-cost"}
POINTERS = {
    "threshold_curve": f"{THRESHOLD_ARTIFACT}:$.threshold_curve",
    "hardgate_checks": f"{THRESHOLD_ARTIFACT}:$.hardgate.checks",
    "hardgate_policy": f"{THRESHOLD_ARTIFACT}:$.hardgate.policy",
    "control_baseline": f"{THRESHOLD_ARTIFACT}:$.threshold_summary.control_baseline",
    "not_claimed": f"{THRESHOLD_ARTIFACT}:$.applicability_boundary.not_claimed",
}


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _at(source: Mapping[str, Any], *path: str) -> Any:
    current: Any = source
    for key in path:
        if not isinstance(current, Mapping):
            return None
        current = current.get(key)
    return current


def _keys(value: Any):
    if isinstance(value, Mapping):
        for key, cell in value.items():
            yield str(key)
            yield from _keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _keys(cell)


def validate_source_integrity(threshold_payload: Mapping[str, Any]) -> tuple[bool, list[str]]:
    failures: list[str] = []
    curve = _at(threshold_payload, "threshold_curve")
    if not isinstance(curve, list):
        failures.append("missing $.threshold_curve")
    elif len(curve) != 19:
        failures.append(f"$.threshold_curve length {len(curve)} != 19")
    elif not all(isinstance(cell, Mapping) and {"threshold", "metrics"} <= set(cell) for cell in curve):
        failures.append("$.threshold_curve cells must expose threshold and metrics")
    if not isinstance(_at(threshold_payload, "hardgate", "checks"), Mapping):
        failures.append("missing $.hardgate.checks")
    if not isinstance(_at(threshold_payload, "hardgate", "policy"), Mapping):
        failures.append("missing $.hardgate.policy")
    return not failures, failures


def _auroc_ci_low(cell: Mapping[str, Any]) -> float | None:
    value = _at(cell, "metrics", "AUROC", "ci95_low")
    if isinstance(value, bool) or value is None:
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def select_positive_threshold_cell(threshold_payload: Mapping[str, Any]) -> tuple[dict[str, Any] | None, str | None]:
    curve = _at(threshold_payload, "threshold_curve")
    for index, cell in enumerate(curve if isinstance(curve, list) else []):
        if isinstance(cell, Mapping) and (_auroc_ci_low(cell) or 0.0) > 0.5:
            return dict(cell), f"{THRESHOLD_ARTIFACT}:$.threshold_curve[{index}]"
    return None, None


def build_pseudo_payload(threshold_payload: Mapping[str, Any]) -> dict[str, Any]:
    cell, source_pointer = select_positive_threshold_cell(threshold_payload)
    main = {"positive_discovery": cell is not None, "structural_discovery": False, "shift_information": 0.0, "surface_delta_count": 0}
    if cell is None:
        policy = _at(threshold_payload, "hardgate", "policy") or {}
        basis = {
            "source_pointer": POINTERS["hardgate_policy"],
            "positive_auroc_rule": policy.get("positive_auroc_rule", POSITIVE_RULE) if isinstance(policy, Mapping) else POSITIVE_RULE,
            "reason": "no deterministic positive threshold cell is available",
        }
        return {
            "artifact": JSON_ARTIFACT,
            "verdict": "negative/compression",
            "positive_discovery": False,
            "single_threshold_basis": [],
            "bounded_policy_basis": basis,
            "main_verdict": main,
        }
    basis = {
        "source_pointer": source_pointer,
        "threshold": cell["threshold"],
        "positive_rule": POSITIVE_RULE,
        "positive_signal": {"metric": "AUROC", "ci95_low": _auroc_ci_low(cell), "comparison": "> 0.5"},
    }
    return {
        "artifact": JSON_ARTIFACT,
        "verdict": "positive-discovery",
        "positive_discovery": True,
        "single_threshold_basis": [basis],
        "main_verdict": main,
    }


def validate_single_threshold_basis(pseudo_payload: Mapping[str, Any]) -> tuple[bool, list[str]]:
    failures: list[str] = []
    basis = pseudo_payload.get("single_threshold_basis")
    if pseudo_payload.get("positive_discovery") is True:
        if not isinstance(basis, list) or len(basis) != 1:
            failures.append("positive pseudo payload must carry exactly one single_threshold_basis cell")
        elif not isinstance(basis[0], Mapping) or not str(basis[0].get("source_pointer", "")).startswith(f"{THRESHOLD_ARTIFACT}:$.threshold_curve["):
            failures.append("single_threshold_basis source pointer must target one threshold curve cell")
        for forbidden in ("adjacent", "adjacent_run", "adjacent_thresholds", "positive_thresholds"):
            if forbidden in set(_keys(basis)):
                failures.append(f"single_threshold_basis must not inherit {forbidden}")
    return not failures, failures


def validate_control_and_claim_boundary(threshold_payload: Mapping[str, Any], pseudo_payload: Mapping[str, Any]) -> tuple[bool, list[str]]:
    failures: list[str] = []
    if not isinstance(_at(threshold_payload, "threshold_summary", "control_baseline"), list):
        failures.append("missing $.threshold_summary.control_baseline")
    if not isinstance(_at(threshold_payload, "applicability_boundary", "not_claimed"), list):
        failures.append("missing $.applicability_boundary.not_claimed")
    forbidden_keys = sorted(set(_keys(pseudo_payload)) & FORBIDDEN_CLAIM_KEYS)
    if forbidden_keys:
        failures.append(f"claim-bearing pseudo payload contains forbidden score fields: {forbidden_keys}")
    text = json.dumps(pseudo_payload, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    if hits:
        failures.append(f"claim-bearing pseudo payload contains forbidden positive claim terms: {hits}")
    return not failures, failures


def evaluate_pseudo_payload(pseudo_payload: Mapping[str, Any]) -> dict[str, Any]:
    projection = assign_discovery_level(pseudo_payload)
    terminal_verdict = str(pseudo_payload.get("verdict", ""))
    escaped = terminal_verdict == "positive-discovery" or projection.discovery_level in ESCAPE_LEVELS
    return {
        "terminal_verdict": terminal_verdict,
        "discovery_level": projection.discovery_level,
        "discovery_reasons": list(projection.reasons),
        "escaped": escaped,
        "escaped_positive_is_discovery_evidence": False,
        "status": "escaped-positive-captured" if escaped else "checked-fail-closed",
    }


def _base(generated_at: str | None, hardgates: Mapping[str, Any], status: str) -> dict[str, Any]:
    return {
        "schema_id": LOCAL_SCHEMA_ID,
        "artifact": JSON_ARTIFACT,
        "report": MARKDOWN_ARTIFACT,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "status": status,
        "canonical_role": CANONICAL_ROLE,
        "escape_semantics": "escaped positive is gate failure evidence, not discovery evidence",
        "hardgates": dict(hardgates),
    }


def _gate(status: bool, **extra: Any) -> dict[str, Any]:
    return {"status": "pass" if status else "fail", **extra}


def _escaped_row(pseudo: Mapping[str, Any], projection: Mapping[str, Any]) -> list[dict[str, Any]]:
    if not projection["escaped"]:
        return []
    basis = pseudo["single_threshold_basis"][0]
    return [{
        "kind": "single_threshold_escape_witness",
        "source_pointer": basis["source_pointer"],
        "positive_signal": basis["positive_signal"],
        "terminal_verdict": projection["terminal_verdict"],
        "discovery_level": projection["discovery_level"],
        "reason": "escaped positive captured as gate failure evidence, not discovery evidence",
    }]


def build_sidecar(*, root: Path | None = None, generated_at: str | None = None) -> dict[str, Any]:
    base = root or ROOT
    threshold_payload = _load(base / THRESHOLD_ARTIFACT)
    hardgates: dict[str, dict[str, Any]] = {}
    source_ok, source_failures = validate_source_integrity(threshold_payload)
    hardgates["HG-STEW-1"] = _gate(source_ok, source_pointers=[POINTERS[key] for key in ("threshold_curve", "hardgate_checks", "hardgate_policy")], failures=source_failures)
    if not source_ok:
        return _base(generated_at, hardgates, "source-integrity-failed")

    pseudo = build_pseudo_payload(threshold_payload)
    basis_ok, basis_failures = validate_single_threshold_basis(pseudo)
    boundary_ok, boundary_failures = validate_control_and_claim_boundary(threshold_payload, pseudo)
    projection = evaluate_pseudo_payload(pseudo)
    hardgates.update(
        {
            "HG-STEW-2": _gate(basis_ok, criterion="single_threshold_basis is exactly one checked threshold cell and the only positive basis", failures=basis_failures),
            "HG-STEW-3": {"status": "pass", "criterion": "positive-discovery or D4/D5 is captured as gate failure evidence", "projection": projection},
            "HG-STEW-5": _gate(boundary_ok, source_pointers=[POINTERS["control_baseline"], POINTERS["not_claimed"]], failures=boundary_failures),
            "HG-STEW-6": {"status": "pass", "criterion": "single-threshold evidence is never promoted as discovery by this sidecar", "promotion": "none"},
        }
    )
    payload = _base(generated_at, hardgates, projection["status"] if basis_ok and boundary_ok else "construction-failed")
    payload.update(
        {
            "source_artifacts": {
                "threshold_frontier": THRESHOLD_ARTIFACT,
                "projector": "bedc_quality_lab.research_discovery.assign_discovery_level",
                "claim_terms": "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS",
            },
            "source_pointers": dict(POINTERS),
            "single_threshold_basis": pseudo.get("single_threshold_basis", []),
            "bounded_policy_basis": pseudo.get("bounded_policy_basis"),
            "projection": projection,
            "escaped_rows": _escaped_row(pseudo, projection),
            "not_claimed": list(_at(threshold_payload, "applicability_boundary", "not_claimed") or []),
            "sidecar_not_claimed": ["No threshold tuning claim.", "No D5 claim.", "No canonical discovery-map promotion.", "No model-quality solution claim."],
            "revoke_conditions": ["threshold policy changes so single-threshold readiness is unavailable or actively covered", "control baseline pointer is missing", "forbidden claim term or score field appears in claim-bearing fields"],
        }
    )
    return payload


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Single Threshold Escape Witness",
        "",
        f"- artifact: `{payload['artifact']}`",
        f"- schema_id: `{payload['schema_id']}`",
        f"- canonical_role: `{payload['canonical_role']}`",
        f"- status: `{payload['status']}`",
        f"- projection: `{payload.get('projection', {}).get('discovery_level', 'unavailable')}`",
        "- escaped_positive_is_discovery_evidence: `false`",
        "",
        "## Source Pointers",
        "",
    ]
    lines += [f"- {key}: `{pointer}`" for key, pointer in sorted(payload.get("source_pointers", {}).items())]
    lines += ["", "## Hardgates", ""]
    lines += [f"- {name}: `{row['status']}`" for name, row in payload["hardgates"].items()]
    lines += ["", "## Basis", ""]
    if payload.get("single_threshold_basis"):
        for cell in payload["single_threshold_basis"]:
            signal = cell["positive_signal"]
            lines.append(f"- {cell['source_pointer']}: threshold={cell['threshold']}, {signal['metric']}.ci95_low={signal['ci95_low']}")
    else:
        lines.append("- No positive single-threshold cell was selected.")
    lines += ["", "## Boundary", ""]
    lines += [f"- {item}" for item in payload.get("sidecar_not_claimed", [])]
    return "\n".join(lines) + "\n"


def write_sidecar(root: Path, payload: Mapping[str, Any]) -> tuple[Path, Path]:
    json_path = root / JSON_ARTIFACT
    md_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_markdown(payload), encoding="utf-8")
    return json_path, md_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    payload = build_sidecar(root=args.root)
    json_path, md_path = write_sidecar(args.root, payload)
    print(f"wrote {json_path}")
    print(f"wrote {md_path}")
    print(f"status {payload['status']}")
    return 0 if payload["status"] in {"escaped-positive-captured", "checked-fail-closed"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
