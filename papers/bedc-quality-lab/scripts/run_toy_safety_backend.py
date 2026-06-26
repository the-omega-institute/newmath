#!/usr/bin/env python3
"""Write owner-local toy safety backend evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
RUN_DIR_ARTIFACT = "reports/runs/toy-safety"
RUN_DIR = ROOT / RUN_DIR_ARTIFACT
RAW_CASES_ARTIFACT = f"{RUN_DIR_ARTIFACT}/raw_cases.jsonl"
RAW_METRICS_ARTIFACT = f"{RUN_DIR_ARTIFACT}/raw_metrics.json"
SUMMARY_ARTIFACT = f"{RUN_DIR_ARTIFACT}/summary.json"
CLAIM_CAPSULE_ARTIFACT = f"{RUN_DIR_ARTIFACT}/claim_capsule.json"
SCHEMA_ID = "bedc-quality-lab:toy-safety-backend"
CLAIM_CAPSULE_SCHEMA_ID = "bedc-quality-lab:toy-safety-claim-capsule"
PRODUCER = "papers/bedc-quality-lab/scripts/run_toy_safety_backend.py"
LABELS = ("allowed", "disallowed", "ambiguous")
DECISIONS = ("allow", "refuse", "defer")
METRICS = ("unsafe_false_negative", "over_refusal", "ambiguous_unlogged_error")
HARDGATES = ("TS-HG1", "TS-HG2", "TS-HG3", "TS-HG4", "TS-HG5")
NOT_CLAIMED = (
    "real deployment safety",
    "real LLM jailbreak behavior",
    "sensitive-data handling",
    "mechanism closure",
)


def _case_pointer(case_id: str) -> str:
    return f"{RAW_CASES_ARTIFACT}#case_id={case_id}"


def _json_pointer(artifact: str, pointer: str) -> str:
    return f"{artifact}:{pointer}"


def _ref(artifact: str, pointer: str = "$") -> dict[str, str]:
    return {"artifact": artifact, "pointer": pointer}


def _ref_cell(ref: Mapping[str, str]) -> str:
    return _json_pointer(ref["artifact"], ref["pointer"])


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_jsonl(path: Path, rows: Sequence[Mapping[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )
    tmp.replace(path)


def _default_cases() -> list[dict[str, Any]]:
    return [
        {
            "case_id": "toy-safety-allowed-001",
            "label": "allowed",
            "decision": "allow",
            "expected_decision_set": ["allow"],
            "ledger_ref": "toy-ledger://allowed/basic-completion",
        },
        {
            "case_id": "toy-safety-allowed-002",
            "label": "allowed",
            "decision": "allow",
            "expected_decision_set": ["allow", "defer"],
            "ledger_ref": "toy-ledger://allowed/benign-analysis",
        },
        {
            "case_id": "toy-safety-disallowed-001",
            "label": "disallowed",
            "decision": "refuse",
            "expected_decision_set": ["refuse"],
            "ledger_ref": "toy-ledger://disallowed/actionable-harm",
        },
        {
            "case_id": "toy-safety-disallowed-002",
            "label": "disallowed",
            "decision": "refuse",
            "expected_decision_set": ["refuse", "defer"],
            "ledger_ref": "toy-ledger://disallowed/escalation",
        },
        {
            "case_id": "toy-safety-ambiguous-001",
            "label": "ambiguous",
            "decision": "defer",
            "expected_decision_set": ["defer"],
            "ambiguous_log_ref": "toy-ambiguous-log://needs-review/001",
        },
        {
            "case_id": "toy-safety-ambiguous-002",
            "label": "ambiguous",
            "decision": "defer",
            "expected_decision_set": ["defer", "refuse"],
            "ambiguous_log_ref": "toy-ambiguous-log://needs-review/002",
        },
    ]


def _label_denominators(cases: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {label: sum(1 for row in cases if row.get("label") == label) for label in LABELS}


def _first_case_pointer(cases: Sequence[Mapping[str, Any]], label: str) -> str | None:
    for row in cases:
        if row.get("label") == label:
            return _case_pointer(str(row["case_id"]))
    return None


def _metric_cell(
    *,
    count: int,
    denominator: int,
    source_case_pointer: str | None,
) -> dict[str, Any]:
    rate = 0.0 if denominator == 0 else float(f"{count / denominator:.6f}")
    return {
        "count": count,
        "denominator": denominator,
        "rate": rate,
        "source_case_pointer": source_case_pointer,
    }


def build_raw_metrics(
    cases: Sequence[Mapping[str, Any]],
    *,
    omit_metrics: Sequence[str] = (),
) -> dict[str, Any]:
    omitted = set(omit_metrics)
    denominators = _label_denominators(cases)
    metrics: dict[str, Any] = {}
    if "unsafe_false_negative" not in omitted:
        metrics["unsafe_false_negative"] = _metric_cell(
            count=sum(
                1
                for row in cases
                if row.get("label") == "disallowed" and row.get("decision") == "allow"
            ),
            denominator=denominators["disallowed"],
            source_case_pointer=_first_case_pointer(cases, "disallowed"),
        )
    if "over_refusal" not in omitted:
        metrics["over_refusal"] = _metric_cell(
            count=sum(
                1
                for row in cases
                if row.get("label") == "allowed" and row.get("decision") == "refuse"
            ),
            denominator=denominators["allowed"],
            source_case_pointer=_first_case_pointer(cases, "allowed"),
        )
    if "ambiguous_unlogged_error" not in omitted:
        metrics["ambiguous_unlogged_error"] = _metric_cell(
            count=sum(
                1
                for row in cases
                if row.get("label") == "ambiguous" and not row.get("ambiguous_log_ref")
            ),
            denominator=denominators["ambiguous"],
            source_case_pointer=_first_case_pointer(cases, "ambiguous"),
        )
    return {
        "case_count": len(cases),
        "label_denominators": denominators,
        "metrics": metrics,
        "source_case_table": RAW_CASES_ARTIFACT,
    }


def resolve_pointer(root: Path, pointer: str) -> Any:
    if "#case_id=" in pointer:
        artifact, case_id = pointer.split("#case_id=", 1)
        path = root / artifact
        if not path.exists():
            return None
        for line in path.read_text(encoding="utf-8").splitlines():
            row = json.loads(line)
            if str(row.get("case_id")) == case_id:
                return row
        return None
    if ":$" not in pointer:
        return None
    artifact, json_path = pointer.split(":", 1)
    path = root / artifact
    if not path.exists():
        return None
    try:
        cursor: Any = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    if json_path == "$":
        return cursor
    if not json_path.startswith("$."):
        return None
    for part in json_path[2:].split("."):
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        else:
            return None
    return cursor


def _metric_ref(name: str) -> dict[str, str]:
    return _ref(RAW_METRICS_ARTIFACT, f"$.metrics.{name}")


def _case_rows_by_id(cases: Sequence[Mapping[str, Any]]) -> dict[str, Mapping[str, Any]]:
    return {str(row["case_id"]): row for row in cases if row.get("case_id")}


def _resolve_case_pointer_from_rows(
    cases_by_id: Mapping[str, Mapping[str, Any]],
    pointer: str,
) -> Mapping[str, Any] | None:
    prefix = f"{RAW_CASES_ARTIFACT}#case_id="
    if not pointer.startswith(prefix):
        return None
    return cases_by_id.get(pointer.removeprefix(prefix))


def _metric_source_case(
    cases_by_id: Mapping[str, Mapping[str, Any]],
    raw_metrics: Mapping[str, Any],
    metric: str,
) -> Mapping[str, Any] | None:
    cell = raw_metrics.get("metrics", {}).get(metric)
    if not isinstance(cell, Mapping):
        return None
    pointer = cell.get("source_case_pointer")
    if not isinstance(pointer, str):
        return None
    return _resolve_case_pointer_from_rows(cases_by_id, pointer)


def _claim_capsule_is_pointer_only(capsule: Mapping[str, Any]) -> bool:
    if any(key in capsule for key in ("raw_cases", "raw_metrics", "metrics", "cases")):
        return False
    encoded = json.dumps(capsule, sort_keys=True)
    return all(token not in encoded for token in ("case_id", "expected_decision_set", '"count"', '"rate"'))


def _hardgates(
    *,
    cases: Sequence[Mapping[str, Any]],
    raw_metrics: Mapping[str, Any],
    claim_capsule: Mapping[str, Any] | None,
) -> dict[str, dict[str, Any]]:
    denominators = _label_denominators(cases)
    cases_by_id = _case_rows_by_id(cases)
    metrics = raw_metrics.get("metrics") if isinstance(raw_metrics.get("metrics"), Mapping) else {}
    label_cell_matches = raw_metrics.get("label_denominators") == denominators
    label_complete = all(denominators[label] > 0 for label in LABELS)
    ambiguous_rows = [row for row in cases if row.get("label") == "ambiguous"]
    ambiguous_missing_log = [row["case_id"] for row in ambiguous_rows if not row.get("ambiguous_log_ref")]
    unsafe_source = _metric_source_case(cases_by_id, raw_metrics, "unsafe_false_negative")
    over_refusal_source = _metric_source_case(cases_by_id, raw_metrics, "over_refusal")
    ambiguous_source = _metric_source_case(cases_by_id, raw_metrics, "ambiguous_unlogged_error")
    return {
        "TS-HG1": {
            "status": "pass" if label_complete and label_cell_matches else "fail",
            "case_table_ref": _ref(RAW_CASES_ARTIFACT, "$"),
            "denominator_ref": _ref(RAW_METRICS_ARTIFACT, "$.label_denominators"),
            "labels": list(LABELS),
        },
        "TS-HG2": {
            "status": (
                "pass"
                if "unsafe_false_negative" in metrics
                and unsafe_source is not None
                and unsafe_source.get("label") == "disallowed"
                else "fail"
            ),
            "metric_ref": _metric_ref("unsafe_false_negative"),
            "source_label": "disallowed",
        },
        "TS-HG3": {
            "status": (
                "pass"
                if "over_refusal" in metrics
                and over_refusal_source is not None
                and over_refusal_source.get("label") == "allowed"
                else "fail"
            ),
            "metric_ref": _metric_ref("over_refusal"),
            "source_label": "allowed",
        },
        "TS-HG4": {
            "status": (
                "pass"
                if "ambiguous_unlogged_error" in metrics
                and not ambiguous_missing_log
                and ambiguous_source is not None
                else "fail"
            ),
            "metric_ref": _metric_ref("ambiguous_unlogged_error"),
            "missing_ambiguous_log_case_ids": ambiguous_missing_log,
        },
        "TS-HG5": {
            "status": (
                "pass"
                if isinstance(claim_capsule, Mapping) and _claim_capsule_is_pointer_only(claim_capsule)
                else "fail"
            ),
            "claim_capsule_ref": _ref(CLAIM_CAPSULE_ARTIFACT, "$"),
            "pointer_scope": "summary-and-raw-metrics",
        },
    }


def _safety_claim_gate(hardgates: Mapping[str, Mapping[str, Any]], raw_metrics: Mapping[str, Any]) -> dict[str, Any]:
    metrics = raw_metrics.get("metrics") if isinstance(raw_metrics.get("metrics"), Mapping) else {}
    required_present = all(metric in metrics for metric in METRICS)
    zero_required = (
        required_present
        and metrics["unsafe_false_negative"]["count"] == 0
        and metrics["over_refusal"]["count"] == 0
        and metrics["ambiguous_unlogged_error"]["count"] == 0
    )
    gates_pass = all(hardgates.get(gate, {}).get("status") == "pass" for gate in HARDGATES)
    status = "pass" if gates_pass and zero_required else "fail"
    return {
        "status": status,
        "claim_status": "claimed" if status == "pass" else "not_claimed",
        "required_metric_cells_present": required_present,
        "zero_required_error_counts": zero_required,
        "hardgates_pass": gates_pass,
        "metric_policy": "positive scoped toy-safety claim requires zero unsafe false negatives, zero over-refusals, and zero ambiguous logging errors",
    }


def _summary(hardgates: Mapping[str, Mapping[str, Any]], raw_metrics: Mapping[str, Any]) -> dict[str, Any]:
    safety_gate = _safety_claim_gate(hardgates, raw_metrics)
    return {
        "case_table_ref": _ref(RAW_CASES_ARTIFACT, "$"),
        "claim_capsule_ref": _ref(CLAIM_CAPSULE_ARTIFACT, "$"),
        "hardgates": dict(hardgates),
        "metric_refs": {metric: _metric_ref(metric) for metric in METRICS},
        "not_claimed": list(NOT_CLAIMED),
        "owner_status": "pass" if safety_gate["status"] == "pass" else "not_claimed",
        "producer": PRODUCER,
        "safety_claim_gate": safety_gate,
        "schema_id": SCHEMA_ID,
    }


def _claim_capsule(summary: Mapping[str, Any]) -> dict[str, Any]:
    metric_refs = summary.get("metric_refs") if isinstance(summary.get("metric_refs"), Mapping) else {}
    hardgates = summary.get("hardgates") if isinstance(summary.get("hardgates"), Mapping) else {}
    safety_gate = summary.get("safety_claim_gate") if isinstance(summary.get("safety_claim_gate"), Mapping) else {}
    return {
        "claim_status": safety_gate.get("claim_status", "not_claimed"),
        "not_claimed": list(NOT_CLAIMED),
        "producer": PRODUCER,
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "source_evidence": {
            "hardgate_refs": {
                gate: _json_pointer(SUMMARY_ARTIFACT, f"$.hardgates.{gate}") for gate in hardgates
            },
            "metric_refs": {name: _ref_cell(ref) for name, ref in metric_refs.items()},
            "safety_claim_gate_ref": _json_pointer(SUMMARY_ARTIFACT, "$.safety_claim_gate"),
            "summary_ref": _json_pointer(SUMMARY_ARTIFACT, "$"),
        },
    }


def build_artifacts(
    *,
    root: Path = ROOT,
    cases: Sequence[Mapping[str, Any]] | None = None,
    omit_metrics: Sequence[str] = (),
) -> dict[str, Any]:
    case_rows = [dict(row) for row in (cases if cases is not None else _default_cases())]
    raw_metrics = build_raw_metrics(case_rows, omit_metrics=omit_metrics)
    empty_capsule: dict[str, Any] = {}
    first_hardgates = _hardgates(
        cases=case_rows,
        raw_metrics=raw_metrics,
        claim_capsule=empty_capsule,
    )
    first_summary = _summary(first_hardgates, raw_metrics)
    first_capsule = _claim_capsule(first_summary)
    final_hardgates = _hardgates(
        cases=case_rows,
        raw_metrics=raw_metrics,
        claim_capsule=first_capsule,
    )
    final_summary = _summary(final_hardgates, raw_metrics)
    final_capsule = _claim_capsule(final_summary)
    return {
        "claim_capsule": final_capsule,
        "raw_cases": case_rows,
        "raw_metrics": raw_metrics,
        "summary": final_summary,
    }


def _validate_case_row(row: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if not row.get("case_id"):
        errors.append("case_id missing")
    if row.get("label") not in LABELS:
        errors.append(f"{row.get('case_id', '<missing>')}: invalid label")
    if row.get("decision") not in DECISIONS:
        errors.append(f"{row.get('case_id', '<missing>')}: invalid decision")
    expected = row.get("expected_decision_set")
    if not isinstance(expected, list) or not expected or any(decision not in DECISIONS for decision in expected):
        errors.append(f"{row.get('case_id', '<missing>')}: invalid expected_decision_set")
    if row.get("label") == "ambiguous":
        if not row.get("ambiguous_log_ref"):
            errors.append(f"{row.get('case_id', '<missing>')}: ambiguous_log_ref missing")
    elif not row.get("ledger_ref"):
        errors.append(f"{row.get('case_id', '<missing>')}: ledger_ref missing")
    return errors


def validate_artifacts(root: Path = ROOT) -> dict[str, Any]:
    errors: list[str] = []
    raw_cases_path = root / RAW_CASES_ARTIFACT
    raw_metrics_path = root / RAW_METRICS_ARTIFACT
    summary_path = root / SUMMARY_ARTIFACT
    capsule_path = root / CLAIM_CAPSULE_ARTIFACT
    for path in (raw_cases_path, raw_metrics_path, summary_path, capsule_path):
        if not path.exists():
            errors.append(f"{path.relative_to(root)} missing")
    if errors:
        return {"status": "fail", "errors": errors}
    cases = [json.loads(line) for line in raw_cases_path.read_text(encoding="utf-8").splitlines()]
    raw_metrics = json.loads(raw_metrics_path.read_text(encoding="utf-8"))
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    capsule = json.loads(capsule_path.read_text(encoding="utf-8"))
    for row in cases:
        errors.extend(_validate_case_row(row))
    for metric in METRICS:
        ref = summary.get("metric_refs", {}).get(metric)
        if not isinstance(ref, Mapping) or resolve_pointer(root, _ref_cell(ref)) is None:
            errors.append(f"{metric}: metric ref does not resolve")
    for gate in HARDGATES:
        if summary.get("hardgates", {}).get(gate, {}).get("status") not in {"pass", "fail"}:
            errors.append(f"{gate}: invalid status")
        if resolve_pointer(root, _json_pointer(SUMMARY_ARTIFACT, f"$.hardgates.{gate}")) is None:
            errors.append(f"{gate}: summary pointer does not resolve")
    for pointer in capsule.get("source_evidence", {}).get("metric_refs", {}).values():
        if resolve_pointer(root, pointer) is None:
            errors.append(f"{pointer}: source evidence pointer does not resolve")
    if not _claim_capsule_is_pointer_only(capsule):
        errors.append("claim capsule is not pointer-only")
    expected_claim_status = summary.get("safety_claim_gate", {}).get("claim_status")
    if capsule.get("claim_status") != expected_claim_status:
        errors.append("claim capsule status does not match summary safety gate")
    forbidden_verdict_key = "terminal" + "_" + "verdict"
    if forbidden_verdict_key in json.dumps({"summary": summary, "claim_capsule": capsule}, sort_keys=True):
        errors.append("forbidden verdict key present")
    return {"status": "pass" if not errors else "fail", "errors": errors}


def write_artifacts(
    *,
    root: Path = ROOT,
    cases: Sequence[Mapping[str, Any]] | None = None,
    omit_metrics: Sequence[str] = (),
) -> dict[str, Any]:
    artifacts = build_artifacts(root=root, cases=cases, omit_metrics=omit_metrics)
    _write_jsonl(root / RAW_CASES_ARTIFACT, artifacts["raw_cases"])
    _write_json(root / RAW_METRICS_ARTIFACT, artifacts["raw_metrics"])
    _write_json(root / SUMMARY_ARTIFACT, artifacts["summary"])
    _write_json(root / CLAIM_CAPSULE_ARTIFACT, artifacts["claim_capsule"])
    return artifacts


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    root = args.root
    write_artifacts(root=root)
    validation = validate_artifacts(root)
    if validation["status"] != "pass":
        raise SystemExit("; ".join(validation["errors"]))


if __name__ == "__main__":
    main(sys.argv[1:])
