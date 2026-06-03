#!/usr/bin/env python3
"""Build the canonical report discovery map."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.research_discovery import DiscoveryLevel, assign_discovery_level
from scripts.run_canonical_reports import CANONICAL_REPORTS, CanonicalReportSpec


DISCOVERY_MAP_SCHEMA_ID = "bedc-quality-lab:canonical-discovery-map"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_MARKDOWN_ARTIFACT = "reports/canonical/discovery_map.md"
DISCOVERY_MAP_ARTIFACT_ID = "bedc-quality-lab:discovery-map"
DISCOVERY_LEVELS: tuple[DiscoveryLevel, ...] = ("D0", "D1", "D2", "D3", "D4", "D5", "DN", "DR")


@dataclass(frozen=True)
class ProjectionEvidence:
    projection_status: str
    evidence_pointer: str | None = None
    control_pointer: str | None = None
    failed_gate: str | None = None
    debt_row_pointer: str | None = None


def _root(root: Path | None) -> Path:
    return ROOT if root is None else root


def _artifact_path(relative_path: str, *, root: Path | None = None) -> Path:
    return _root(root) / relative_path


def _load_payload(spec: CanonicalReportSpec, *, root: Path | None = None) -> dict[str, Any]:
    path = _artifact_path(spec.json_artifact, root=root)
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"canonical report payload must be a JSON object: {spec.json_artifact}")
    return payload


def pointer_value(payload: Mapping[str, Any], pointer: str | None) -> Any:
    if pointer is None or not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        elif isinstance(cursor, list) and part.isdigit() and int(part) < len(cursor):
            cursor = cursor[int(part)]
        else:
            return None
    return cursor


def _after_minus_before_debt_delta(payload: Mapping[str, Any]) -> float | None:
    cell = pointer_value(payload, "$.deltas.after_minus_before.debt_delta")
    return float(cell) if isinstance(cell, (int, float)) and not isinstance(cell, bool) else None


def _verdict_debt_delta(payload: Mapping[str, Any]) -> float | None:
    cell = pointer_value(payload, "$.verdicts.0.deltas.debt_delta")
    return float(cell) if isinstance(cell, (int, float)) and not isinstance(cell, bool) else None


def _has_nonempty_cell(payload: Mapping[str, Any], pointer: str) -> bool:
    cell = pointer_value(payload, pointer)
    if cell is None:
        return False
    if isinstance(cell, (Mapping, list, tuple, str)):
        return len(cell) > 0
    return True


def _gap_head_on_h_projection(payload: Mapping[str, Any], spec: CanonicalReportSpec) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    evidence_pointer = "$.treatment_verdict.positive"
    if pointer_value(payload, evidence_pointer) is True:
        overlay["positive_discovery"] = True
        return overlay, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=evidence_pointer,
            control_pointer=spec.control_pointer,
        )
    return overlay, ProjectionEvidence(projection_status="source-insufficient", evidence_pointer=evidence_pointer)


def _gap_head_discovery_projection(
    payload: Mapping[str, Any], spec: CanonicalReportSpec
) -> tuple[dict[str, Any], ProjectionEvidence]:
    if pointer_value(payload, "$.positive_discovery") is True:
        return {}, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.positive_discovery",
            control_pointer=spec.control_pointer,
        )
    return {}, ProjectionEvidence(projection_status="source-insufficient", evidence_pointer="$.positive_discovery")


def _gap_head_robustness_projection(
    payload: Mapping[str, Any], spec: CanonicalReportSpec
) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    if pointer_value(payload, "$.acceptance_gates.status") == "pass" and pointer_value(payload, "$.final_status") == "pass":
        overlay["positive_discovery"] = True
        return overlay, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.acceptance_gates.status",
            control_pointer=spec.control_pointer,
        )
    return overlay, ProjectionEvidence(projection_status="source-insufficient", evidence_pointer="$.acceptance_gates.status")


def _certificate_training_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    status = pointer_value(payload, "$.result.status")
    debt_delta = _after_minus_before_debt_delta(payload)
    if status == "negative":
        overlay["verdict"] = "rejected"
    if debt_delta is not None:
        overlay["main_verdict"] = {"deltas": {"debt_delta": debt_delta}}
    if pointer_value(payload, "$.claim_gate.audit_improvement_tradeoff") is True:
        overlay["claim_gate"] = {"training_audit_improvement_tradeoff": True}
    if status == "negative":
        return overlay, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.result.status",
            debt_row_pointer="$.deltas.after_minus_before.debt_delta",
        )
    if debt_delta is not None or pointer_value(payload, "$.claim_gate.audit_improvement_tradeoff") is True:
        return overlay, ProjectionEvidence(projection_status="projected", debt_row_pointer="$.deltas.after_minus_before.debt_delta")
    return overlay, ProjectionEvidence(projection_status="source-insufficient")


def _certificate_discovery_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    status = pointer_value(payload, "$.main_claim_status")
    if status == "observed-negative" and pointer_value(payload, "$.positive_discovery") is False:
        overlay["verdict"] = "rejected"
    debt_delta = _verdict_debt_delta(payload)
    if debt_delta is not None:
        overlay["main_verdict"] = {"deltas": {"debt_delta": debt_delta}}
    if pointer_value(payload, "$.claim_gate.training_audit_improvement_tradeoff") is True:
        overlay["claim_gate"] = {"training_audit_improvement_tradeoff": True}
    if "verdict" in overlay:
        return overlay, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.positive_discovery",
            debt_row_pointer="$.verdicts.0.deltas.debt_delta",
        )
    if debt_delta is not None or pointer_value(payload, "$.claim_gate.training_audit_improvement_tradeoff") is True:
        return overlay, ProjectionEvidence(projection_status="projected", debt_row_pointer="$.verdicts.0.deltas.debt_delta")
    return overlay, ProjectionEvidence(projection_status="source-insufficient")


def _gap_head_ablation_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    if pointer_value(payload, "$.hardgate.status") == "fail":
        return {"verdict": "rejected"}, ProjectionEvidence(projection_status="projected", failed_gate="$.hardgate.status")
    return {}, ProjectionEvidence(projection_status="source-insufficient", failed_gate="$.hardgate.status")


def _spectral_ablation_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    status = pointer_value(payload, "$.ledger_summary.status")
    control = pointer_value(payload, "$.negative_control_summary.treatment_better_than_all_controls")
    if status == "negative" or control is False:
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.negative_control_summary.treatment_better_than_all_controls",
        )
    return {}, ProjectionEvidence(
        projection_status="source-insufficient",
        failed_gate="$.negative_control_summary.treatment_better_than_all_controls",
    )


def _debt_cell_projection(payload: Mapping[str, Any], pointer: str) -> tuple[dict[str, Any], ProjectionEvidence]:
    if _has_nonempty_cell(payload, pointer):
        return {"main_verdict": {"deltas": {"debt_delta": -1.0}}}, ProjectionEvidence(
            projection_status="projected",
            debt_row_pointer=pointer,
        )
    return {}, ProjectionEvidence(projection_status="source-insufficient", debt_row_pointer=pointer)


def _projection_overlay_and_evidence(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    if spec.name == "gap-head-on-h":
        overlay, evidence = _gap_head_on_h_projection(payload, spec)
    elif spec.name == "gap-head-discovery":
        overlay, evidence = _gap_head_discovery_projection(payload, spec)
    elif spec.name == "gap-head-robustness-sweep":
        overlay, evidence = _gap_head_robustness_projection(payload, spec)
    elif spec.name == "certificate-guided-training":
        overlay, evidence = _certificate_training_projection(payload)
    elif spec.name == "certificate-guided-discovery":
        overlay, evidence = _certificate_discovery_projection(payload)
    elif spec.name == "gap-head-ablation":
        overlay, evidence = _gap_head_ablation_projection(payload)
    elif spec.name == "spectral-ablation-hinge":
        overlay, evidence = _spectral_ablation_projection(payload)
    elif spec.name == "anisotropic-ou-sweep":
        overlay, evidence = _debt_cell_projection(payload, "$.transition_debt_by_grid")
    elif spec.name == "nongaussian-distribution-sweep":
        overlay, evidence = _debt_cell_projection(payload, "$.negative_result_ledger")
    elif spec.name == "mixing-family-sweep":
        overlay, evidence = _debt_cell_projection(payload, "$.coverage_item.debt_item")
    else:
        overlay, evidence = {}, ProjectionEvidence(projection_status="source-insufficient")
    return overlay, evidence


def projection_payload(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> dict[str, Any]:
    """Copy a canonical payload and overlay only classifier-readable lab fields."""

    overlay, _evidence = _projection_overlay_and_evidence(spec, payload)
    projected = dict(payload)
    projected.update(overlay)
    return projected


def _projection_evidence(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> ProjectionEvidence:
    _overlay, evidence = _projection_overlay_and_evidence(spec, payload)
    return evidence


def _audit_row(spec: CanonicalReportSpec, payload: Mapping[str, Any], level: DiscoveryLevel, evidence: ProjectionEvidence) -> tuple[str, str]:
    if level not in DISCOVERY_LEVELS:
        return "invalid", "missing-discovery-level"
    if level in {"D4", "D5"}:
        if evidence.control_pointer is None:
            return "invalid", "missing-control-pointer"
        if pointer_value(payload, evidence.control_pointer) is None:
            return "invalid", "unresolved-control-pointer"
    if level == "DN":
        if evidence.failed_gate is None:
            return "invalid", "missing-failed-gate"
        if pointer_value(payload, evidence.failed_gate) is None:
            return "invalid", "unresolved-failed-gate"
    if level == "D1":
        if evidence.debt_row_pointer is None:
            return "invalid", "missing-debt-row-pointer"
        if pointer_value(payload, evidence.debt_row_pointer) is None:
            return "invalid", "unresolved-debt-row-pointer"
    return "valid", ""


def discovery_row(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> dict[str, Any]:
    projected = projection_payload(spec, payload)
    evidence = _projection_evidence(spec, payload)
    verdict = assign_discovery_level(projected)
    audit_status, audit_reason = _audit_row(spec, payload, verdict.discovery_level, evidence)
    row: dict[str, Any] = {
        "report": spec.name,
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "discovery_level": verdict.discovery_level,
        "terminal_verdict": verdict.terminal_verdict,
        "classifier_reasons": list(verdict.reasons),
        "projection_status": evidence.projection_status,
        "evidence_pointer": evidence.evidence_pointer,
        "audit_status": audit_status,
        "audit_reason": audit_reason,
    }
    if evidence.control_pointer is not None:
        row["control_pointer"] = evidence.control_pointer
    if evidence.failed_gate is not None:
        row["failed_gate"] = evidence.failed_gate
    if evidence.debt_row_pointer is not None:
        row["debt_row_pointer"] = evidence.debt_row_pointer
    return row


def _manifest_audit(
    *,
    root: Path | None = None,
    canonical_reports: Sequence[CanonicalReportSpec] | None = None,
) -> dict[str, Any]:
    reports = CANONICAL_REPORTS if canonical_reports is None else canonical_reports
    registered = {spec.json_artifact for spec in reports}
    registered_pointer_artifacts = {"reports/canonical/quality-scorecard.json", DISCOVERY_MAP_JSON_ARTIFACT}
    directory_json = {
        f"reports/canonical/{path.name}"
        for path in sorted((_root(root) / "reports" / "canonical").glob("*.json"))
        if path.name != "index.json"
    }
    return {
        "unregistered_json_artifacts": sorted(directory_json - registered - registered_pointer_artifacts),
    }


def _level_counts(rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {level: sum(1 for row in rows if row.get("discovery_level") == level) for level in DISCOVERY_LEVELS}


def build_discovery_map(
    *,
    generated_at: str | None = None,
    root: Path | None = None,
    canonical_reports: Sequence[CanonicalReportSpec] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    reports = CANONICAL_REPORTS if canonical_reports is None else canonical_reports
    rows = [discovery_row(spec, _load_payload(spec, root=root)) for spec in reports]
    return {
        "schema_id": DISCOVERY_MAP_SCHEMA_ID,
        "artifact_id": DISCOVERY_MAP_ARTIFACT_ID,
        "generated_at": timestamp,
        "json_artifact": DISCOVERY_MAP_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_MAP_MARKDOWN_ARTIFACT,
        "row_count": len(rows),
        "level_counts": _level_counts(rows),
        "manifest_audit": _manifest_audit(root=root, canonical_reports=reports),
        "rows": rows,
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Discovery Map",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Rows: `{payload['row_count']}`",
        "",
        "| report | level | projection | audit | evidence |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        pointer = row.get("control_pointer") or row.get("failed_gate") or row.get("debt_row_pointer") or row.get("evidence_pointer")
        pointer_display = pointer if pointer is not None else row["projection_status"]
        lines.append(
            "| "
            f"`{row['report']}` | "
            f"`{row['discovery_level']}` | "
            f"`{row['projection_status']}` | "
            f"`{row['audit_status']}` | "
            f"`{pointer_display}` |"
        )
    lines.append("")
    return "\n".join(lines)


def write_discovery_map(
    *,
    generated_at: str | None = None,
    root: Path | None = None,
    canonical_reports: Sequence[CanonicalReportSpec] | None = None,
) -> dict[str, Any]:
    payload = build_discovery_map(generated_at=generated_at, root=root, canonical_reports=canonical_reports)
    json_path = _artifact_path(DISCOVERY_MAP_JSON_ARTIFACT, root=root)
    markdown_path = _artifact_path(DISCOVERY_MAP_MARKDOWN_ARTIFACT, root=root)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict-manifest-audit", action="store_true", help="Exit nonzero on invalid rows or unregistered JSON artifacts.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_discovery_map()
    invalid_rows = [row for row in payload["rows"] if row["audit_status"] != "valid"]
    unregistered = payload["manifest_audit"]["unregistered_json_artifacts"]
    if args.strict_manifest_audit and (invalid_rows or unregistered):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
