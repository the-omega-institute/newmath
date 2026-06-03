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
    robustness_pointer: str | None = None
    adversarial_pointer: str | None = None
    observed_debt_transfer_pointer: str | None = None
    d5_readiness: "GapHeadD5ReadinessLedger | None" = None


@dataclass(frozen=True)
class GapHeadD5Criterion:
    name: str
    status: str
    artifact: str
    pointer: str | None
    reason: str


@dataclass(frozen=True)
class GapHeadD5ReadinessLedger:
    criteria: tuple[GapHeadD5Criterion, ...]

    @property
    def all_pass(self) -> bool:
        return all(criterion.status == "pass" for criterion in self.criteria)

    def as_dict(self) -> dict[str, dict[str, str | None]]:
        return {
            criterion.name: {
                "name": criterion.name,
                "status": criterion.status,
                "artifact": criterion.artifact,
                "pointer": criterion.pointer,
                "reason": criterion.reason,
            }
            for criterion in self.criteria
        }


GAP_HEAD_ROBUSTNESS_ARTIFACT = "reports/canonical/gap-head-robustness-sweep.json"
NEGATIVE_WITNESSES_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
OBSERVED_DEBT_ARTIFACT = "reports/canonical/gap-head-observed-debt-transfer.json"
DIMENSION_MISMATCH_TRANSFER_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.json"
GAP_HEAD_D5_CONTEXT_ARTIFACTS = (
    GAP_HEAD_ROBUSTNESS_ARTIFACT,
    NEGATIVE_WITNESSES_ARTIFACT,
    OBSERVED_DEBT_ARTIFACT,
)
GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER = "$.gap_head_on_h_observed_debt_transfer.status"
DIMENSION_MISMATCH_TRANSFER_POINTER = "$.dimension_mismatch_debt_transfer.status"


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


def _load_artifact_payload(relative_path: str, *, root: Path | None = None) -> dict[str, Any]:
    path = _artifact_path(relative_path, root=root)
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"canonical report payload must be a JSON object: {relative_path}")
    return payload


def _load_gap_head_d5_context(*, root: Path | None = None) -> dict[str, dict[str, Any]]:
    return {artifact: _load_artifact_payload(artifact, root=root) for artifact in GAP_HEAD_D5_CONTEXT_ARTIFACTS}


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


def _criterion(
    name: str,
    status: str,
    artifact: str,
    pointer: str | None,
    reason: str,
) -> GapHeadD5Criterion:
    return GapHeadD5Criterion(name=name, status=status, artifact=artifact, pointer=pointer, reason=reason)


def _artifact_pointer(artifact: str, pointer: str | None) -> str | None:
    return f"{artifact}:{pointer}" if pointer is not None else None


def _readiness_pointer(ledger: GapHeadD5ReadinessLedger, name: str) -> str | None:
    for criterion in ledger.criteria:
        if criterion.name == name:
            return _artifact_pointer(criterion.artifact, criterion.pointer)
    return None


def _gap_head_d5_readiness(context: Mapping[str, Mapping[str, Any]]) -> GapHeadD5ReadinessLedger:
    robustness = context.get(GAP_HEAD_ROBUSTNESS_ARTIFACT, {})
    negative = context.get(NEGATIVE_WITNESSES_ARTIFACT, {})
    observed = context.get(OBSERVED_DEBT_ARTIFACT, {})

    final_status_pass = pointer_value(robustness, "$.final_status") == "pass"
    threshold_pass = pointer_value(robustness, "$.A1_threshold_sweep.treatment_verdict.positive") is True and final_status_pass
    ablation_pass = pointer_value(robustness, "$.A2_feature_ablation.status") == "complete" and final_status_pass
    seed_pass = (
        pointer_value(robustness, "$.A3_seed_expansion.status") == "complete"
        and pointer_value(robustness, "$.A3_seed_expansion.final_verdict") == "robust_positive"
        and final_status_pass
    )

    witnesses = pointer_value(negative, "$.witnesses")
    expected_kind_count = pointer_value(negative, "$.expected_kind_count")
    witness_kinds = {row.get("kind") for row in witnesses if isinstance(row, Mapping)} if isinstance(witnesses, list) else set()
    terminal_verdicts = {row.get("terminal_verdict") for row in witnesses if isinstance(row, Mapping)} if isinstance(witnesses, list) else set()
    adversarial_pass = (
        pointer_value(negative, "$.status") == "pointer-only"
        and isinstance(expected_kind_count, int)
        and len(witness_kinds) == expected_kind_count == 8
        and terminal_verdicts <= {"rejected", "demoted", "ledger-only"}
    )

    observed_transfer_status = pointer_value(observed, GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER)
    observed_transfer_pass = observed_transfer_status == "pass"

    return GapHeadD5ReadinessLedger(
        criteria=(
            _criterion(
                "threshold",
                "pass" if threshold_pass else "missing",
                GAP_HEAD_ROBUSTNESS_ARTIFACT,
                "$.A1_threshold_sweep.treatment_verdict.positive",
                "A1 threshold sweep passes under the canonical robustness final_status."
                if threshold_pass
                else "A1 threshold sweep pass pointer is absent or not positive under final_status=pass.",
            ),
            _criterion(
                "ablation",
                "pass" if ablation_pass else "missing",
                GAP_HEAD_ROBUSTNESS_ARTIFACT,
                "$.A2_feature_ablation.status",
                "A2 feature ablation is complete under the canonical robustness final_status."
                if ablation_pass
                else "A2 feature ablation pass pointer is absent or not complete under final_status=pass.",
            ),
            _criterion(
                "seed_expansion",
                "pass" if seed_pass else "missing",
                GAP_HEAD_ROBUSTNESS_ARTIFACT,
                "$.A3_seed_expansion.final_verdict",
                "A3 seed expansion has robust_positive final verdict under final_status=pass."
                if seed_pass
                else "A3 seed expansion pass pointer is absent or not robust_positive under final_status=pass.",
            ),
            _criterion(
                "adversarial",
                "pass" if adversarial_pass else "failed",
                NEGATIVE_WITNESSES_ARTIFACT,
                "$.witnesses",
                "The eight adversarial witness kinds do not break the discovery gate."
                if adversarial_pass
                else "Adversarial witnesses are missing, incomplete, or contain a gate-breaking terminal verdict.",
            ),
            _criterion(
                "observed_debt_transfer",
                "pass" if observed_transfer_pass else "missing",
                OBSERVED_DEBT_ARTIFACT,
                GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER,
                "Observed-debt transfer metric for gap-head-on-h passes."
                if observed_transfer_pass
                else "Observed-debt sweep covers observed-debt surfaces but has no gap-head-on-h observed-debt transfer metric.",
            ),
        )
    )


def _gap_head_on_h_projection(
    payload: Mapping[str, Any],
    spec: CanonicalReportSpec,
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    evidence_pointer = "$.treatment_verdict.positive"
    ledger = _gap_head_d5_readiness({} if context is None else context)
    if pointer_value(payload, evidence_pointer) is True:
        overlay["positive_discovery"] = True
        if ledger.all_pass:
            overlay["acceptance_gates"] = {"status": "pass"}
            overlay["final_status"] = "pass"
        return overlay, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=evidence_pointer,
            control_pointer=spec.control_pointer,
            robustness_pointer=_readiness_pointer(ledger, "threshold"),
            adversarial_pointer=_readiness_pointer(ledger, "adversarial"),
            observed_debt_transfer_pointer=_readiness_pointer(ledger, "observed_debt_transfer"),
            d5_readiness=ledger,
        )
    return overlay, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer=evidence_pointer,
        robustness_pointer=_readiness_pointer(ledger, "threshold"),
        adversarial_pointer=_readiness_pointer(ledger, "adversarial"),
        observed_debt_transfer_pointer=_readiness_pointer(ledger, "observed_debt_transfer"),
        d5_readiness=ledger,
    )


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


def _dimension_mismatch_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    status = pointer_value(payload, DIMENSION_MISMATCH_TRANSFER_POINTER)
    if status == "pass":
        return {"positive_discovery": True}, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
            control_pointer="$.control_protocol",
        )
    if status == "failed":
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
            failed_gate=DIMENSION_MISMATCH_TRANSFER_POINTER,
        )
    return {}, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
    )


def _projection_overlay_and_evidence(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    if spec.name == "gap-head-on-h":
        overlay, evidence = _gap_head_on_h_projection(payload, spec, context)
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


def projection_payload(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Copy a canonical payload and overlay only classifier-readable lab fields."""

    overlay, _evidence = _projection_overlay_and_evidence(spec, payload, context)
    projected = dict(payload)
    projected.update(overlay)
    return projected


def _projection_evidence(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> ProjectionEvidence:
    _overlay, evidence = _projection_overlay_and_evidence(spec, payload, context)
    return evidence


def _unresolved_d5_criterion(evidence: ProjectionEvidence, context: Mapping[str, Mapping[str, Any]]) -> str | None:
    ledger = evidence.d5_readiness
    if ledger is None:
        return "missing-d5-readiness"
    recalculated = _gap_head_d5_readiness(context)
    recalculated_status = {criterion.name: criterion.status for criterion in recalculated.criteria}
    for criterion in ledger.criteria:
        if criterion.status != "pass":
            return f"d5-readiness-{criterion.name}-{criterion.status}"
        if criterion.pointer is None:
            return f"missing-d5-pointer-{criterion.name}"
        payload = context.get(criterion.artifact, {})
        if pointer_value(payload, criterion.pointer) is None:
            return f"unresolved-d5-pointer-{criterion.name}"
        if recalculated_status.get(criterion.name) != "pass":
            return f"d5-readiness-{criterion.name}-failed"
    return None


def _audit_row(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    level: DiscoveryLevel,
    evidence: ProjectionEvidence,
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[str, str]:
    if level not in DISCOVERY_LEVELS:
        return "invalid", "missing-discovery-level"
    if level in {"D4", "D5"}:
        if evidence.control_pointer is None:
            return "invalid", "missing-control-pointer"
        if pointer_value(payload, evidence.control_pointer) is None:
            return "invalid", "unresolved-control-pointer"
        if level == "D5" and spec.name == "gap-head-on-h":
            reason = _unresolved_d5_criterion(evidence, {} if context is None else context)
            if reason is not None:
                return "invalid", reason
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


def discovery_row(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    context_payloads = {} if context is None else context
    projected = projection_payload(spec, payload, context_payloads)
    evidence = _projection_evidence(spec, payload, context_payloads)
    verdict = assign_discovery_level(projected)
    audit_status, audit_reason = _audit_row(spec, payload, verdict.discovery_level, evidence, context_payloads)
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
    if evidence.robustness_pointer is not None:
        row["robustness_pointer"] = evidence.robustness_pointer
    if evidence.adversarial_pointer is not None:
        row["adversarial_pointer"] = evidence.adversarial_pointer
    if evidence.observed_debt_transfer_pointer is not None:
        row["observed_debt_transfer_pointer"] = evidence.observed_debt_transfer_pointer
    if evidence.d5_readiness is not None:
        row["d5_readiness"] = evidence.d5_readiness.as_dict()
    return row


def _manifest_audit(
    *,
    root: Path | None = None,
    canonical_reports: Sequence[CanonicalReportSpec] | None = None,
) -> dict[str, Any]:
    reports = CANONICAL_REPORTS if canonical_reports is None else canonical_reports
    registered = {spec.json_artifact for spec in reports}
    registered_pointer_artifacts = {
        "reports/canonical/quality-scorecard.json",
        "reports/canonical/formal_hardening.json",
        DISCOVERY_MAP_JSON_ARTIFACT,
        NEGATIVE_WITNESSES_ARTIFACT,
        OBSERVED_DEBT_ARTIFACT,
        DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
    }
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
    gap_head_d5_context = _load_gap_head_d5_context(root=root)
    rows = [discovery_row(spec, _load_payload(spec, root=root), gap_head_d5_context) for spec in reports]
    dimension_payload = _load_artifact_payload(DIMENSION_MISMATCH_TRANSFER_ARTIFACT, root=root)
    if dimension_payload:
        rows.append(_dimension_mismatch_discovery_row(dimension_payload))
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


def _dimension_mismatch_discovery_row(payload: Mapping[str, Any]) -> dict[str, Any]:
    overlay, evidence = _dimension_mismatch_projection(payload)
    projected = dict(payload)
    projected.update(overlay)
    verdict = assign_discovery_level(projected)
    audit_status, audit_reason = _dimension_mismatch_audit_row(payload, verdict.discovery_level, evidence)
    row: dict[str, Any] = {
        "report": "dimension-mismatch-debt-transfer",
        "json_artifact": DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        "markdown_artifact": "reports/canonical/dimension-mismatch-debt-transfer.md",
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
    return row


def _dimension_mismatch_audit_row(
    payload: Mapping[str, Any],
    level: DiscoveryLevel,
    evidence: ProjectionEvidence,
) -> tuple[str, str]:
    if level == "D5":
        return "invalid", "dimension-mismatch-transfer-has-no-d5-shortcut"
    if level == "D4":
        if evidence.control_pointer is None:
            return "invalid", "missing-control-pointer"
        if pointer_value(payload, evidence.control_pointer) is None:
            return "invalid", "unresolved-control-pointer"
    if level == "DN":
        if evidence.failed_gate is None:
            return "invalid", "missing-failed-gate"
        if pointer_value(payload, evidence.failed_gate) is None:
            return "invalid", "unresolved-failed-gate"
    return "valid", ""


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
    readiness_rows = [row for row in payload["rows"] if row.get("d5_readiness")]
    if readiness_rows:
        lines.extend(["", "## D5 readiness", ""])
        for row in readiness_rows:
            lines.extend([f"### {row['report']}", ""])
            for name, criterion in row["d5_readiness"].items():
                lines.append(
                    "- "
                    f"`{name}`: `{criterion['status']}` "
                    f"({criterion['artifact']}:{criterion['pointer']}) "
                    f"{criterion['reason']}"
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
