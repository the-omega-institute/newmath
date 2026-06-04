#!/usr/bin/env python3
"""Build the canonical report discovery map."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import math
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
    canonical_discovery_level: DiscoveryLevel | None = None
    canonical_terminal_verdict: str | None = None


@dataclass(frozen=True)
class AttributionCapsuleLevels:
    base_level: str
    base_status: str
    mechanism_level: str
    mechanism_status: str
    mechanism_channel: str
    failed_gate: str | None
    operational_pointer: str
    mechanism_pointer: str
    mechanism_case_pointer: str


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
DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER = "$.dimension_mismatch_debt_transfer.effective_level"
DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER = "$.dimension_mismatch_debt_transfer.anti_triviality_status"
ATTRIBUTION_CAPSULE_OPERATIONAL_POINTER = "$.d5_o"
ATTRIBUTION_CAPSULE_MECHANISM_POINTER = "$.d5_m"
ATTRIBUTION_CAPSULE_MECHANISM_CASE_POINTER = "$.mechanism_case"


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


def _finite_number_cell(payload: Mapping[str, Any], pointer: str) -> float:
    cell = pointer_value(payload, pointer)
    if isinstance(cell, bool) or not isinstance(cell, (int, float)):
        raise ValueError(f"transfer artifact numeric cell is missing or non-numeric: {pointer}")
    value = float(cell)
    if not math.isfinite(value):
        raise ValueError(f"transfer artifact numeric cell is non-finite: {pointer}")
    return value


def _non_stub_not_claimed(payload: Mapping[str, Any]) -> bool:
    not_claimed = pointer_value(payload, "$.not_claimed")
    if not isinstance(not_claimed, list) or not not_claimed:
        return False
    stub_terms = {"fixture", "stub", "todo", "tbd"}
    normalized_items: list[str] = []
    for item in not_claimed:
        if not isinstance(item, str) or not item.strip():
            return False
        normalized_items.append(item.strip().lower())
    return not set(normalized_items).issubset(stub_terms)


def assert_transfer_artifact_integrity(
    payload: Mapping[str, Any],
    *,
    status_pointer: str,
    learned_auroc_pointer: str,
    matched_random_auroc_pointer: str,
    control_positive_pointer: str,
) -> None:
    if pointer_value(payload, status_pointer) != "pass":
        raise ValueError("transfer artifact status is not pass")
    if pointer_value(payload, control_positive_pointer) is not False:
        raise ValueError("transfer artifact control arm is missing or positive")
    _finite_number_cell(payload, f"{learned_auroc_pointer}.mean")
    learned_ci95_low = _finite_number_cell(payload, f"{learned_auroc_pointer}.ci95_low")
    _finite_number_cell(payload, f"{learned_auroc_pointer}.ci95_high")
    _finite_number_cell(payload, f"{matched_random_auroc_pointer}.mean")
    _finite_number_cell(payload, f"{matched_random_auroc_pointer}.ci95_low")
    matched_random_ci95_high = _finite_number_cell(payload, f"{matched_random_auroc_pointer}.ci95_high")
    if learned_ci95_low <= matched_random_ci95_high:
        raise ValueError("transfer artifact lacks learned-over-matched-random AUROC evidence")
    if not _non_stub_not_claimed(payload):
        raise ValueError("transfer artifact not_claimed boundary is missing or stubbed")


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

    try:
        assert_transfer_artifact_integrity(
            observed,
            status_pointer=GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER,
            learned_auroc_pointer="$.surfaces.0.hardgates.HG-A1.learned_auroc",
            matched_random_auroc_pointer="$.surfaces.0.hardgates.HG-A1.matched_random_auroc",
            control_positive_pointer="$.surfaces.0.control_verdict.positive",
        )
        observed_transfer_pass = True
    except ValueError:
        observed_transfer_pass = False

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
                else "Observed-debt transfer artifact is missing, malformed, stubbed, or lacks learned-over-matched-random control evidence.",
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


def _sigreg_training_proxy_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    consistency = _sigreg_training_proxy_consistency(payload)
    status = pointer_value(payload, "$.result.status")
    debt_delta = pointer_value(payload, "$.d1_evidence.debt_delta")
    if consistency[0] and status == "d1-pointer-accepted" and isinstance(debt_delta, (int, float)) and not isinstance(debt_delta, bool):
        return {
            "verdict": "d1-pointer-accepted",
            "main_verdict": {"deltas": {"debt_delta": float(debt_delta)}},
        }, ProjectionEvidence(
            projection_status="projected",
            debt_row_pointer="$.d1_evidence.debt_delta",
        )
    if status == "negative" or not consistency[0]:
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            failed_gate=consistency[2],
            debt_row_pointer="$.d1_evidence.debt_delta",
        )
    return {}, ProjectionEvidence(projection_status="source-insufficient", debt_row_pointer="$.d1_evidence.debt_delta")


def _sigreg_failed_gate_pointer(payload: Mapping[str, Any]) -> str:
    failed_gate = pointer_value(payload, "$.failed_gate")
    if isinstance(failed_gate, str) and failed_gate:
        return f"$.d1_evidence.d1_hardgates.{failed_gate}.status"
    hardgates = pointer_value(payload, "$.d1_evidence.d1_hardgates")
    if isinstance(hardgates, Mapping):
        for name, row in hardgates.items():
            if isinstance(name, str) and isinstance(row, Mapping) and row.get("status") != "pass":
                return f"$.d1_evidence.d1_hardgates.{name}.status"
    return "$.hardgate.status"


def _sigreg_training_proxy_consistency(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    hardgates = pointer_value(payload, "$.d1_evidence.d1_hardgates")
    if not isinstance(hardgates, Mapping) or not hardgates:
        return False, "missing-d1-hardgates", "$.d1_evidence.d1_hardgates"

    failed_gates = [
        name
        for name, row in hardgates.items()
        if not isinstance(row, Mapping) or row.get("status") != "pass"
    ]
    all_pass = not failed_gates
    result_status = pointer_value(payload, "$.result.status")
    result_level = pointer_value(payload, "$.result.discovery_level")
    result_terminal = pointer_value(payload, "$.result.terminal_verdict")
    claim_gate_status = pointer_value(payload, "$.claim_gate.status")
    hardgate_status = pointer_value(payload, "$.hardgate.status")
    claim_tradeoff = pointer_value(payload, "$.claim_gate.training_audit_improvement_tradeoff")
    failed_gate = pointer_value(payload, "$.failed_gate")
    hardgate_failed_gate = pointer_value(payload, "$.hardgate.failed_gate")
    capsule_status = pointer_value(payload, "$.result.claim_capsule_status")
    forbidden_audit_status = pointer_value(payload, "$.forbidden_claim_term_audit.status")
    if all_pass:
        expected = {
            "result_status": "d1-pointer-accepted",
            "result_level": "D1",
            "result_terminal": "d1-pointer-accepted",
            "claim_gate_status": "pass",
            "hardgate_status": "pass",
            "claim_tradeoff": True,
            "failed_gate": None,
            "hardgate_failed_gate": None,
            "capsule_status": "d1-pointer-accepted",
            "forbidden_audit_status": "pass",
        }
    else:
        expected_failed = failed_gates[0]
        expected = {
            "result_status": "negative",
            "result_level": "DN",
            "result_terminal": "rejected",
            "claim_gate_status": "fail",
            "hardgate_status": "fail",
            "claim_tradeoff": False,
            "failed_gate": expected_failed,
            "hardgate_failed_gate": expected_failed,
            "capsule_status": "failed",
        }

    observed = {
        "result_status": result_status,
        "result_level": result_level,
        "result_terminal": result_terminal,
        "claim_gate_status": claim_gate_status,
        "hardgate_status": hardgate_status,
        "claim_tradeoff": claim_tradeoff,
        "failed_gate": failed_gate,
        "hardgate_failed_gate": hardgate_failed_gate,
        "capsule_status": capsule_status,
        "forbidden_audit_status": forbidden_audit_status,
    }
    for key, expected_value in expected.items():
        if observed[key] != expected_value:
            return False, f"sigreg-{key}-mismatch", _sigreg_failed_gate_pointer(payload)
    if forbidden_audit_status != "pass":
        hg5 = hardgates.get("D1-HG5")
        if all_pass or not isinstance(hg5, Mapping) or hg5.get("status") != "fail":
            return False, "sigreg-forbidden_audit_status-mismatch", "$.forbidden_claim_term_audit.status"
    if all_pass:
        debt_delta = pointer_value(payload, "$.d1_evidence.debt_delta")
        if not isinstance(debt_delta, (int, float)) or isinstance(debt_delta, bool) or float(debt_delta) >= 0.0:
            return False, "sigreg-debt-delta-mismatch", "$.d1_evidence.debt_delta"
    return True, "", _sigreg_failed_gate_pointer(payload)


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
    effective_level = pointer_value(payload, DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER)
    terminal_verdict = pointer_value(payload, "$.dimension_mismatch_debt_transfer.terminal_verdict")
    anti_triviality_status = pointer_value(payload, DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER)
    if status == "pass":
        try:
            assert_transfer_artifact_integrity(
                payload,
                status_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
                learned_auroc_pointer="$.hardgate_evidence.HG-B3.learned_auroc",
                matched_random_auroc_pointer="$.hardgate_evidence.HG-B3.matched_random_auroc",
                control_positive_pointer="$.hardgate_evidence.HG-B3.matched_random_positive",
            )
        except ValueError:
            return {}, ProjectionEvidence(
                projection_status="source-insufficient",
                evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
            )
        if effective_level == "DN" and terminal_verdict == "negative_discovery":
            return {"verdict": "rejected"}, ProjectionEvidence(
                projection_status="projected",
                evidence_pointer=DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER,
                failed_gate=DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER,
                canonical_discovery_level="DN",
                canonical_terminal_verdict="negative_discovery",
            )
        if effective_level == "D4" and terminal_verdict == "source_pass":
            return {}, ProjectionEvidence(
                projection_status="projected",
                evidence_pointer=DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER,
                canonical_discovery_level="D4",
                canonical_terminal_verdict="source_pass",
            )
        if anti_triviality_status == "scale_leakage_detected":
            return {"verdict": "rejected"}, ProjectionEvidence(
                projection_status="projected",
                evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
                failed_gate=DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER,
                canonical_discovery_level="DN" if effective_level == "DN" else None,
                canonical_terminal_verdict=terminal_verdict if isinstance(terminal_verdict, str) else None,
            )
    if status == "failed":
        canonical_level = effective_level if isinstance(effective_level, str) and effective_level in DISCOVERY_LEVELS else None
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
            failed_gate=DIMENSION_MISMATCH_TRANSFER_POINTER,
            canonical_discovery_level=canonical_level,
            canonical_terminal_verdict=terminal_verdict if isinstance(terminal_verdict, str) else None,
        )
    return {}, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
    )


def _mechanism_channel(status: Any) -> str | None:
    if not isinstance(status, str):
        return None
    prefix = "D5-O retained, mechanism = "
    if status.startswith(prefix):
        return status.removeprefix(prefix)
    return None


def _attribution_capsule_levels(payload: Mapping[str, Any]) -> AttributionCapsuleLevels | None:
    d5_o = pointer_value(payload, ATTRIBUTION_CAPSULE_OPERATIONAL_POINTER)
    d5_m = pointer_value(payload, ATTRIBUTION_CAPSULE_MECHANISM_POINTER)
    mechanism_case = pointer_value(payload, ATTRIBUTION_CAPSULE_MECHANISM_CASE_POINTER)
    if not isinstance(d5_o, Mapping) or not isinstance(d5_m, Mapping) or not isinstance(mechanism_case, Mapping):
        return None
    base_status = d5_o.get("status")
    mechanism_status = d5_m.get("status")
    failed_gate = d5_m.get("failed_gate")
    channel = _mechanism_channel(mechanism_case.get("status"))
    if base_status == "ready" and mechanism_status == "blocked" and isinstance(failed_gate, str) and channel:
        return AttributionCapsuleLevels(
            base_level="D5-O",
            base_status="ready",
            mechanism_level="blocked",
            mechanism_status="blocked",
            mechanism_channel=channel,
            failed_gate=failed_gate,
            operational_pointer=ATTRIBUTION_CAPSULE_OPERATIONAL_POINTER,
            mechanism_pointer=ATTRIBUTION_CAPSULE_MECHANISM_POINTER,
            mechanism_case_pointer=ATTRIBUTION_CAPSULE_MECHANISM_CASE_POINTER,
        )
    if base_status == "ready" and mechanism_status == "ready" and d5_m.get("passed") is True:
        return AttributionCapsuleLevels(
            base_level="D5-O",
            base_status="ready",
            mechanism_level="D5-M",
            mechanism_status="ready",
            mechanism_channel=channel or "not-recorded",
            failed_gate=None,
            operational_pointer=ATTRIBUTION_CAPSULE_OPERATIONAL_POINTER,
            mechanism_pointer=ATTRIBUTION_CAPSULE_MECHANISM_POINTER,
            mechanism_case_pointer=ATTRIBUTION_CAPSULE_MECHANISM_CASE_POINTER,
        )
    return None


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
    elif spec.name == "sigreg-training-proxy":
        overlay, evidence = _sigreg_training_proxy_projection(payload)
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
    elif spec.name == "gap-head-attribution-capsule":
        overlay, evidence = {}, ProjectionEvidence(
            projection_status="two-axis-recorded",
            evidence_pointer=spec.positive_claim_pointer,
        )
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
    if spec.name == "gap-head-attribution-capsule":
        return {
            "artifact_id": payload.get("artifact_id", spec.name),
            "json_artifact": payload.get("json_artifact", spec.json_artifact),
            **overlay,
        }
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
    if spec.name == "sigreg-training-proxy":
        consistent, reason, _failed_pointer = _sigreg_training_proxy_consistency(payload)
        if not consistent:
            return "invalid", reason
    if spec.name == "gap-head-attribution-capsule":
        levels = _attribution_capsule_levels(payload)
        if levels is None:
            return "invalid", "attribution-capsule-level-cells-missing"
        if pointer_value(payload, levels.operational_pointer) is None:
            return "invalid", "unresolved-operational-pointer"
        if pointer_value(payload, levels.mechanism_pointer) is None:
            return "invalid", "unresolved-mechanism-pointer"
        if pointer_value(payload, levels.mechanism_case_pointer) is None:
            return "invalid", "unresolved-mechanism-case-pointer"
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
    if spec.name == "gap-head-attribution-capsule":
        levels = _attribution_capsule_levels(payload)
        if levels is not None:
            row.update(
                {
                    "base_level": levels.base_level,
                    "base_status": levels.base_status,
                    "mechanism_level": levels.mechanism_level,
                    "mechanism_status": levels.mechanism_status,
                    "mechanism_channel": levels.mechanism_channel,
                    "operational_pointer": levels.operational_pointer,
                    "mechanism_pointer": levels.mechanism_pointer,
                    "mechanism_case_pointer": levels.mechanism_case_pointer,
                }
            )
            if levels.failed_gate is not None:
                row["mechanism_failed_gate"] = levels.failed_gate
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
        "reports/canonical/gap_head_attribution_capsule.json",
        DISCOVERY_MAP_JSON_ARTIFACT,
        NEGATIVE_WITNESSES_ARTIFACT,
        "reports/canonical/discovery_negative_witness_summary.json",
        "reports/canonical/claim_capsule.json",
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
    discovery_level = evidence.canonical_discovery_level or verdict.discovery_level
    terminal_verdict = evidence.canonical_terminal_verdict or verdict.terminal_verdict
    audit_status, audit_reason = _dimension_mismatch_audit_row(payload, discovery_level, terminal_verdict, evidence)
    row: dict[str, Any] = {
        "report": "dimension-mismatch-debt-transfer",
        "json_artifact": DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        "markdown_artifact": "reports/canonical/dimension-mismatch-debt-transfer.md",
        "discovery_level": discovery_level,
        "terminal_verdict": terminal_verdict,
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
    claim = payload.get("dimension_mismatch_debt_transfer")
    if isinstance(claim, Mapping):
        for key in (
            "base_level",
            "anti_triviality_status",
            "effective_level",
            "downgrade_reason",
            "hypothesis",
            "what_was_learned",
            "not_claimed",
        ):
            if key in claim:
                row[key] = claim[key]
    return row


def _dimension_mismatch_audit_row(
    payload: Mapping[str, Any],
    level: DiscoveryLevel,
    terminal_verdict: str,
    evidence: ProjectionEvidence,
) -> tuple[str, str]:
    canonical_effective_level = pointer_value(payload, "$.dimension_mismatch_debt_transfer.effective_level")
    canonical_discovery_level = pointer_value(payload, "$.dimension_mismatch_debt_transfer.discovery_level")
    canonical_terminal_verdict = pointer_value(payload, "$.dimension_mismatch_debt_transfer.terminal_verdict")
    if isinstance(canonical_effective_level, str) and canonical_effective_level in DISCOVERY_LEVELS and level != canonical_effective_level:
        return "invalid", "dimension-mismatch-discovery-level-disagrees-with-canonical-effective-level"
    if isinstance(canonical_discovery_level, str) and canonical_discovery_level in DISCOVERY_LEVELS and level != canonical_discovery_level:
        return "invalid", "dimension-mismatch-discovery-level-disagrees-with-canonical-discovery-level"
    if isinstance(canonical_terminal_verdict, str) and terminal_verdict != canonical_terminal_verdict:
        return "invalid", "dimension-mismatch-terminal-verdict-disagrees-with-canonical"
    if level == "D5":
        return "invalid", "dimension-mismatch-transfer-has-no-d5-shortcut"
    if level == "D4":
        if terminal_verdict == "source_pass" and evidence.failed_gate is None:
            return "valid", ""
        return "invalid", "dimension-mismatch-d4-requires-source-pass"
    if level == "DN":
        if evidence.failed_gate is None:
            return "invalid", "missing-failed-gate"
        if pointer_value(payload, evidence.failed_gate) is None:
            return "invalid", "unresolved-failed-gate"
        if pointer_value(payload, "$.dimension_mismatch_debt_transfer.base_level") == "D4":
            if pointer_value(payload, "$.dimension_mismatch_debt_transfer.effective_level") != "DN":
                return "invalid", "dimension-mismatch-base-d4-without-terminal-dn"
        if pointer_value(payload, DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER) == "scale_leakage_detected":
            if pointer_value(payload, "$.dimension_mismatch_debt_transfer.effective_level") != "DN":
                return "invalid", "scale-leakage-effective-level-not-dn"
    return "valid", ""


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Discovery Map",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Rows: `{payload['row_count']}`",
        "",
        "| report | level | base | mechanism | projection | audit | evidence |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        pointer = row.get("control_pointer") or row.get("failed_gate") or row.get("debt_row_pointer") or row.get("evidence_pointer")
        pointer_display = pointer if pointer is not None else row["projection_status"]
        lines.append(
            "| "
            f"`{row['report']}` | "
            f"`{row['discovery_level']}` | "
            f"`{row.get('base_level', '')}` | "
            f"`{row.get('mechanism_level', '')}` | "
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
