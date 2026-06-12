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


ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_compiler.map import (
    ANTI_TRIVIALITY_FAMILIES,
    COVERAGE_CELL_FIELDS,
    COVERAGE_FORBIDDEN_KEYS,
    COVERAGE_HARDGATE_IDS,
    COVERAGE_POINTER_FIELDS,
    DN_FACT_KEYS,
    DISCOVERY_LEVELS,
    build_discovery_map_payload,
    validate_discovery_map_payload,
)
from bedc_quality_lab.discovery_compiler.anti_triviality import ANTI_TRIVIALITY_POLICY
from bedc_quality_lab.discovery_compiler.negative_reports import (
    DIMENSION_MISMATCH_GAP_WITNESS_POINTER,
    DIMENSION_MISMATCH_REPORT_ID,
)
from bedc_quality_lab.mechanism_attribution import (
    MECHANISM_EVIDENCE_LEVEL_POINTER,
    MECHANISM_EVIDENCE_POINTER,
    mechanism_causal_evidence_ready,
    project_gap_head_mechanism_evidence,
    unresolved_mechanism_evidence_pointers,
)
from bedc_quality_lab.mechanism_dna import (
    JSON_ARTIFACT as MECHANISM_DNA_ARTIFACT,
    REQUIRED_REF_FIELDS as MECHANISM_DNA_REQUIRED_REF_FIELDS,
    mechanism_dna_artifacts,
    mechanism_dna_row_pointer,
)
from bedc_quality_lab.research_discovery import DiscoveryLevel, assign_discovery_level
from bedc_quality_lab.scope import (
    CLOSED_CLAIM_SCOPE_SEAL,
    ScopeExpansionGate,
    scope_claim_payload,
    scope_expansion_gate_for_payload,
)
from bedc_quality_lab.certificate_gated_attention import REQUIRED_PRODUCTION_NOT_CLAIMED
from bedc_quality_lab.backends.current_lab.gap_head_readiness import (
    GAP_HEAD_ABLATION_ARTIFACT,
    GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER,
    GAP_HEAD_ROBUSTNESS_ARTIFACT,
    NEGATIVE_WITNESSES_ARTIFACT,
    OBSERVED_DEBT_ARTIFACT,
    GapHeadD5ReadinessLedger,
    GapHeadOperationalReadinessPolicy,
    _non_stub_not_claimed,
    assert_transfer_artifact_integrity,
)
from scripts.run_canonical_reports import CANONICAL_REPORTS, CanonicalReportSpec


DISCOVERY_MAP_SCHEMA_ID = "bedc-quality-lab:canonical-discovery-map"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_MARKDOWN_ARTIFACT = "reports/canonical/discovery_map.md"
DISCOVERY_MAP_ARTIFACT_ID = "bedc-quality-lab:discovery-map"
CLAIM_COMPLEXITY_ARTIFACT = "reports/canonical/claim_complexity.json"
CLAIM_VERDICTS_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
HIGH_IMPACT_REVIEW_ARTIFACT = "reports/canonical/high-impact-review.json"


@dataclass(frozen=True)
class ProjectionEvidence:
    projection_status: str
    evidence_pointer: str | None = None
    evidence_label: str | None = None
    control_pointer: str | None = None
    scorecard_pointer: str | None = None
    failed_gate: str | None = None
    debt_row_pointer: str | None = None
    robustness_pointer: str | None = None
    adversarial_pointer: str | None = None
    observed_debt_transfer_pointer: str | None = None
    d5_readiness: "GapHeadD5ReadinessLedger | None" = None
    canonical_terminal_verdict: str | None = None


@dataclass(frozen=True)
class AttributionCapsuleLevels:
    evidence_level: str
    base_level: str
    base_status: str
    mechanism_level: str
    mechanism_status: str
    mechanism_channel: str
    failed_gate: str | None
    operational_pointer: str
    mechanism_pointer: str
    mechanism_case_pointer: str
    mechanism_namecert_pointer: str
    mechanism_ledger_pointer: str
    mechanism_closure_pointer: str


QUALITY_SCORECARD_ARTIFACT = "reports/canonical/quality-scorecard.json"
QUALITY_SCORECARD_ROWS_POINTER = "$.rows"
DIMENSION_MISMATCH_TRANSFER_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.json"
ATTRIBUTION_CAPSULE_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"
GAP_HEAD_D5_CONTEXT_ARTIFACTS = (
    QUALITY_SCORECARD_ARTIFACT,
    GAP_HEAD_ROBUSTNESS_ARTIFACT,
    GAP_HEAD_ABLATION_ARTIFACT,
    NEGATIVE_WITNESSES_ARTIFACT,
    OBSERVED_DEBT_ARTIFACT,
    ATTRIBUTION_CAPSULE_ARTIFACT,
    *mechanism_dna_artifacts(),
    MECHANISM_DNA_ARTIFACT,
)
DIMENSION_MISMATCH_TRANSFER_POINTER = "$.dimension_mismatch_debt_transfer.status"
GAP_HEAD_TRANSFER_ATLAS_DECISION_POINTER = "$.multi_surface_d5_o.decision"
GAP_HEAD_TRANSFER_ATLAS_CONTROL_POINTER = "$.config.control_arm"
ACCEPTED_CLAIM_VERDICT = "accepted_positive_discovery"
POSITIVE_DISCOVERY_GATES_PASS_REASON = "positive-discovery-gates-pass"
MECHANISM_NOT_CLOSED_CLAIM_VERDICT = "mechanism_not_closed"
DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER = "$.dimension_mismatch_debt_transfer.effective_level"
DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER = "$.dimension_mismatch_debt_transfer.anti_triviality_status"
ATTRIBUTION_CAPSULE_OPERATIONAL_POINTER = "$.d5_o"
ATTRIBUTION_CAPSULE_MECHANISM_POINTER = MECHANISM_EVIDENCE_POINTER
ATTRIBUTION_CAPSULE_MECHANISM_CASE_POINTER = "$.mechanism_evidence.candidate_mechanism"
MECHANISM_NAMECERT_LEDGER_POINTER = "$.ledger_debt.0.status"
MECHANISM_NAMECERT_CLOSURE_POINTER = "$.mechanism_evidence.mechanism_status"
MECHANISM_NAMECERT_CANDIDATE_POINTER = "$.mechanism_evidence.candidate_mechanism"
NEGATIVE_DISCOVERY_REPORTS_ARTIFACT = "reports/canonical/negative_discovery_reports.json"
SINGLE_THRESHOLD_ESCAPE_ARTIFACT = "runs/single_threshold_escape_witness.json"
SINGLE_THRESHOLD_ESCAPE_MARKDOWN_ARTIFACT = "runs/single_threshold_escape_witness.md"
TRAINING_CHOICE_OBSERVABILITY_ARTIFACT = "runs/training_choice_observability.json"
TRAINING_CHOICE_OBSERVABILITY_MARKDOWN_ARTIFACT = "runs/training_choice_observability.md"
DISCOVERY_REGULARIZED_TRAINING_ARTIFACT = "reports/canonical/discovery-regularized-training.json"
LEDGER_AWARE_TRANSFORMER_ARTIFACT = "reports/canonical/ledger-aware-transformer.json"
DISCOVERY_GATED_TRANSFORMER_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
SCALING_LADDER_ARTIFACT = "reports/canonical/scaling-ladder.json"
DGT_NEURAL_ABLATION_ARTIFACT = "reports/canonical/dgt-neural-ablation.json"
CERTIFICATE_GATED_ATTENTION_ARTIFACT = "reports/canonical/certificate-gated-attention.json"
MECHANISM_SEEKING_NETWORK_ARTIFACT = "reports/canonical/mechanism-seeking-network.json"
SIGREG_MINI_GRID_ARTIFACT = "reports/canonical/sigreg-mini-grid.json"
LEJEPA_THEOREM_LEDGER_ARTIFACT = "reports/canonical/lejepa_theorem_ledger.json"
MODEL_DESIGN_SUITE_ARTIFACT = "reports/canonical/model_design_suite.json"

DISCOVERY_COVERAGE_SOURCES: tuple[dict[str, str | None], ...] = (
    {
        "component_id": "DGT",
        "canonical_owner_pointer": f"{DISCOVERY_GATED_TRANSFORMER_ARTIFACT}:$",
        "discovery_level_pointer": f"{SCALING_LADDER_ARTIFACT}:$.levels[0]",
        "claim_verdict_pointer": f"{SCALING_LADDER_ARTIFACT}:$.levels[0].owner_decision_pointer",
        "mechanism_certificate_pointer": f"{MECHANISM_DNA_ARTIFACT}:$.rows[3]",
        "debt_pointer": f"{SCALING_LADDER_ARTIFACT}:$.boundary_ledger",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "DGT-neural-ablation",
        "canonical_owner_pointer": f"{DGT_NEURAL_ABLATION_ARTIFACT}:$",
        "discovery_level_pointer": f"{DGT_NEURAL_ABLATION_ARTIFACT}:$.nabl_hardgates.status",
        "claim_verdict_pointer": f"{DGT_NEURAL_ABLATION_ARTIFACT}:$.component_causal_claims",
        "mechanism_certificate_pointer": f"{DGT_NEURAL_ABLATION_ARTIFACT}:$.claim_capsule_ref",
        "debt_pointer": f"{DGT_NEURAL_ABLATION_ARTIFACT}:$.boundary_ledger",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "LAT",
        "canonical_owner_pointer": f"{LEDGER_AWARE_TRANSFORMER_ARTIFACT}:$",
        "discovery_level_pointer": f"{LEDGER_AWARE_TRANSFORMER_ARTIFACT}:$.discovery_map_signal.level_candidate",
        "claim_verdict_pointer": f"{LEDGER_AWARE_TRANSFORMER_ARTIFACT}:$.discovery_map_signal.status",
        "mechanism_certificate_pointer": f"{LEDGER_AWARE_TRANSFORMER_ARTIFACT}:$.mechanism_certificate",
        "debt_pointer": f"{LEDGER_AWARE_TRANSFORMER_ARTIFACT}:$.ledger",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "CGA",
        "canonical_owner_pointer": f"{CERTIFICATE_GATED_ATTENTION_ARTIFACT}:$",
        "discovery_level_pointer": f"{CERTIFICATE_GATED_ATTENTION_ARTIFACT}:$.discovery_map_signal.level_candidate",
        "claim_verdict_pointer": f"{CERTIFICATE_GATED_ATTENTION_ARTIFACT}:$.discovery_map_signal.status",
        "mechanism_certificate_pointer": f"{CERTIFICATE_GATED_ATTENTION_ARTIFACT}:$.certificate_gate_summary",
        "debt_pointer": f"{CERTIFICATE_GATED_ATTENTION_ARTIFACT}:$.revocation_rows",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "DRT",
        "canonical_owner_pointer": f"{DISCOVERY_REGULARIZED_TRAINING_ARTIFACT}:$",
        "discovery_level_pointer": f"{DISCOVERY_REGULARIZED_TRAINING_ARTIFACT}:$.discovery_map_signal.level_candidate",
        "claim_verdict_pointer": f"{DISCOVERY_REGULARIZED_TRAINING_ARTIFACT}:$.discovery_map_signal.status",
        "mechanism_certificate_pointer": f"{MECHANISM_DNA_ARTIFACT}:$.rows[1]",
        "debt_pointer": f"{DISCOVERY_REGULARIZED_TRAINING_ARTIFACT}:$.quality_promotion_boundary",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "MSN",
        "canonical_owner_pointer": f"{MECHANISM_SEEKING_NETWORK_ARTIFACT}:$",
        "discovery_level_pointer": f"{MECHANISM_SEEKING_NETWORK_ARTIFACT}:$.discovery_map_signal.level_candidate",
        "claim_verdict_pointer": f"{MECHANISM_SEEKING_NETWORK_ARTIFACT}:$.discovery_map_signal.status",
        "mechanism_certificate_pointer": f"{MECHANISM_DNA_ARTIFACT}:$.rows[2]",
        "debt_pointer": f"{MECHANISM_SEEKING_NETWORK_ARTIFACT}:$.revocation_rows",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "gap-head-op",
        "canonical_owner_pointer": f"{GAP_HEAD_ROBUSTNESS_ARTIFACT}:$.acceptance_gates.status",
        "discovery_level_pointer": f"{DISCOVERY_MAP_JSON_ARTIFACT}:$.rows[2].discovery_level",
        "claim_verdict_pointer": f"{GAP_HEAD_ROBUSTNESS_ARTIFACT}:$.final_status",
        "mechanism_certificate_pointer": f"{GAP_HEAD_ROBUSTNESS_ARTIFACT}:$.A1_threshold_sweep",
        "debt_pointer": f"{OBSERVED_DEBT_ARTIFACT}:{GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER}",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "gap-head-mech",
        "canonical_owner_pointer": f"{ATTRIBUTION_CAPSULE_ARTIFACT}:$.mechanism_evidence",
        "discovery_level_pointer": f"{ATTRIBUTION_CAPSULE_ARTIFACT}:$.d5_m.status",
        "claim_verdict_pointer": f"{ATTRIBUTION_CAPSULE_ARTIFACT}:$.mechanism_evidence.mechanism_status",
        "mechanism_certificate_pointer": f"{MECHANISM_DNA_ARTIFACT}:$.rows[0]",
        "debt_pointer": f"{ATTRIBUTION_CAPSULE_ARTIFACT}:$.ledger_debt",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "sigreg-mini-grid",
        "canonical_owner_pointer": f"{SIGREG_MINI_GRID_ARTIFACT}:$",
        "discovery_level_pointer": f"{SIGREG_MINI_GRID_ARTIFACT}:$.discovery_map_signal.level_candidate",
        "claim_verdict_pointer": f"{SIGREG_MINI_GRID_ARTIFACT}:$.discovery_map_signal.status",
        "mechanism_certificate_pointer": f"{SIGREG_MINI_GRID_ARTIFACT}:$.trend_summary",
        "debt_pointer": f"{SIGREG_MINI_GRID_ARTIFACT}:$.tradeoff_ledger",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "lejepa-theorem-ledger",
        "canonical_owner_pointer": f"{LEJEPA_THEOREM_LEDGER_ARTIFACT}:$",
        "discovery_level_pointer": f"{LEJEPA_THEOREM_LEDGER_ARTIFACT}:$.result.status",
        "claim_verdict_pointer": f"{LEJEPA_THEOREM_LEDGER_ARTIFACT}:$.claim_gate.status",
        "mechanism_certificate_pointer": f"{LEJEPA_THEOREM_LEDGER_ARTIFACT}:$.theorem_rows",
        "debt_pointer": f"{LEJEPA_THEOREM_LEDGER_ARTIFACT}:$.backend_ledger_rows",
        "negative_witness_pointer": None,
    },
    {
        "component_id": "dimension-mismatch-DN",
        "canonical_owner_pointer": f"{DIMENSION_MISMATCH_TRANSFER_ARTIFACT}:$",
        "discovery_level_pointer": f"{DIMENSION_MISMATCH_TRANSFER_ARTIFACT}:{DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER}",
        "claim_verdict_pointer": f"{DIMENSION_MISMATCH_TRANSFER_ARTIFACT}:$.dimension_mismatch_debt_transfer.terminal_verdict",
        "mechanism_certificate_pointer": None,
        "debt_pointer": f"{DIMENSION_MISMATCH_TRANSFER_ARTIFACT}:{DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER}",
        "negative_witness_pointer": DIMENSION_MISMATCH_GAP_WITNESS_POINTER,
    },
    {
        "component_id": "certificate-guided-DN",
        "canonical_owner_pointer": f"{NEGATIVE_DISCOVERY_REPORTS_ARTIFACT}:$.rows[1]",
        "discovery_level_pointer": f"{NEGATIVE_DISCOVERY_REPORTS_ARTIFACT}:$.rows[1].discovery_level",
        "claim_verdict_pointer": f"{NEGATIVE_DISCOVERY_REPORTS_ARTIFACT}:$.rows[1].terminal_verdict",
        "mechanism_certificate_pointer": None,
        "debt_pointer": f"{CERTIFICATE_GATED_ATTENTION_ARTIFACT}:$.certificate_gate_summary",
        "negative_witness_pointer": f"{NEGATIVE_DISCOVERY_REPORTS_ARTIFACT}:$.rows[1]",
    },
    {
        "component_id": "LeJEPA-mini-grid-DN",
        "canonical_owner_pointer": "reports/runs/lejepa-mini-grid/claim_capsule.json:$",
        "discovery_level_pointer": "reports/runs/lejepa-mini-grid/claim_capsule.json:$.claim_status",
        "claim_verdict_pointer": "reports/runs/lejepa-mini-grid/claim_capsule.json:$.failed_gate",
        "mechanism_certificate_pointer": None,
        "debt_pointer": f"{LEJEPA_THEOREM_LEDGER_ARTIFACT}:$.theorem_rows",
        "negative_witness_pointer": "reports/runs/lejepa-mini-grid/claim_capsule.json:$.run_local.negative_witness[0]",
    },
)
COVERAGE_COMPONENT_IDS = frozenset(str(row["component_id"]) for row in DISCOVERY_COVERAGE_SOURCES)


def _root(root: Path | None) -> Path:
    return ROOT if root is None else root


def _artifact_path(relative_path: str, *, root: Path | None = None) -> Path:
    return _root(root) / relative_path


def _sequence_cell(value: Any) -> Sequence[Any]:
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return value
    return ()


def _pointer_index(rows: Sequence[Any], *, key: str, value: str) -> int | None:
    for index, row in enumerate(rows):
        if isinstance(row, Mapping) and row.get(key) == value:
            return index
    return None


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


def _ensure_negative_sidecar_payloads(*, root: Path | None = None) -> None:
    base = _root(root)
    single_path = base / SINGLE_THRESHOLD_ESCAPE_ARTIFACT
    if not single_path.exists():
        single_path.parent.mkdir(parents=True, exist_ok=True)
        single_path.write_text(
            json.dumps(
                {
                    "schema_id": "bedc-quality-lab:single-threshold-escape-witness-sidecar",
                    "artifact": SINGLE_THRESHOLD_ESCAPE_ARTIFACT,
                    "report": SINGLE_THRESHOLD_ESCAPE_MARKDOWN_ARTIFACT,
                    "status": "checked-fail-closed",
                    "projection": {
                        "discovery_level": "DN",
                        "escaped": False,
                        "escaped_positive_is_discovery_evidence": False,
                        "status": "checked-fail-closed",
                    },
                    "single_threshold_basis": [],
                    "sidecar_not_claimed": ["No threshold tuning claim.", "No D5 claim."],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
    training_path = base / TRAINING_CHOICE_OBSERVABILITY_ARTIFACT
    if not training_path.exists():
        training_path.parent.mkdir(parents=True, exist_ok=True)
        training_path.write_text(
            json.dumps(
                {
                    "schema_id": "bedc-quality-lab:training-choice-observability-sidecar",
                    "artifact": TRAINING_CHOICE_OBSERVABILITY_ARTIFACT,
                    "report": TRAINING_CHOICE_OBSERVABILITY_MARKDOWN_ARTIFACT,
                    "artifact_id": "bedc-quality-lab:training-choice-observability",
                    "status": "pointer-only",
                    "training_choice_observability": {
                        "status": "pointer-only",
                        "observed_debt_arm_count": 0,
                        "ledger_risk_only_arm_count": 1,
                        "boundary_or_invalid_arm_count": 0,
                    },
                    "boundary_ledger": [{"kind": "ledger-risk-only", "failed_gates": ["fixture-boundary"]}],
                    "not_claimed": ["No universal training-choice claim.", "No promotion claim."],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )


def _load_gap_head_d5_context(*, root: Path | None = None) -> dict[str, dict[str, Any]]:
    _ensure_negative_sidecar_payloads(root=root)
    return {artifact: _load_artifact_payload(artifact, root=root) for artifact in GAP_HEAD_D5_CONTEXT_ARTIFACTS}


def _load_claim_verdict_rows(*, root: Path | None = None) -> list[dict[str, Any]]:
    path = _artifact_path(CLAIM_VERDICTS_ARTIFACT, root=root)
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(row, dict):
            rows.append(row)
    return rows


def _scorecard_ready(context: Mapping[str, Mapping[str, Any]]) -> bool:
    scorecard = context.get(QUALITY_SCORECARD_ARTIFACT, {})
    rows = pointer_value(scorecard, QUALITY_SCORECARD_ROWS_POINTER)
    return isinstance(rows, list) and bool(rows) and all(
        isinstance(row, Mapping) and row.get("status") == "ready" for row in rows
    )


THEOREM_DNA_REQUIRED_FIELDS = (
    "theorem_id",
    "assumptions",
    "objects",
    "maps",
    "operators",
    "invariants",
    "proof_dependencies",
    "ledger_debts",
    "formal_status",
)


def _theorem_dna_pointer_cells_resolve(ledger: Mapping[str, Any], cells: Any) -> bool:
    return isinstance(cells, list) and bool(cells) and all(
        isinstance(cell, Mapping)
        and isinstance(cell.get("pointer"), str)
        and pointer_value(ledger, cell["pointer"]) is not None
        for cell in cells
    )


def _theorem_ledger_rows_have_resolvable_dna(context: Mapping[str, Mapping[str, Any]]) -> bool:
    ledger = context.get(LEJEPA_THEOREM_LEDGER_ARTIFACT, {})
    rows = pointer_value(ledger, "$.theorem_rows")
    if not isinstance(rows, list) or not rows:
        return False
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            return False
        pointer = row.get("theorem_dna_pointer")
        if pointer != f"$.theorem_rows[{index}].theorem_dna":
            return False
        dna = pointer_value(ledger, pointer)
        if not isinstance(dna, Mapping):
            return False
        if any(field not in dna for field in THEOREM_DNA_REQUIRED_FIELDS):
            return False
        if dna.get("theorem_id") != row.get("theorem_id", row.get("theorem")):
            return False
        for field in ("assumptions", "ledger_debts", "proof_dependencies"):
            if not _theorem_dna_pointer_cells_resolve(ledger, dna.get(field)):
                return False
    return True


def _mechanism_dna_ref_resolves(row: Mapping[str, Any], field: str, context: Mapping[str, Mapping[str, Any]]) -> bool:
    ref = row.get(field)
    if not isinstance(ref, Mapping):
        return False
    artifact = ref.get("artifact")
    pointer = ref.get("pointer")
    owner_pointer = ref.get("owner_pointer")
    if not all(isinstance(value, str) and value for value in (artifact, pointer, owner_pointer)):
        return False
    if owner_pointer != f"{artifact}:{pointer}":
        return False
    return pointer_value(context.get(artifact, {}), pointer) is not None


def _mechanism_dna_row_ready(report: str, context: Mapping[str, Mapping[str, Any]]) -> bool:
    pointer = mechanism_dna_row_pointer(report)
    if pointer is None or ":" not in pointer:
        return False
    artifact, local_pointer = pointer.split(":", 1)
    payload = context.get(artifact, {})
    row = pointer_value(payload, local_pointer)
    if not isinstance(row, Mapping):
        return False
    if row.get("row_id") != report:
        return False
    if pointer_value(row, "$.row_hardgate.status") != "pass":
        return False
    for field in (*MECHANISM_DNA_REQUIRED_REF_FIELDS, "source_level_ref", "source_status_ref"):
        if not _mechanism_dna_ref_resolves(row, field, context):
            return False
    for forbidden in ("terminal_verdict", "final_verdict", "canonical_terminal_verdict", "core_verdict"):
        if forbidden in json.dumps(row, sort_keys=True):
            return False
    return True


def pointer_value(payload: Mapping[str, Any], pointer: str | None) -> Any:
    if pointer is None or not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                if not isinstance(cursor, Mapping) or key not in cursor:
                    return None
                cursor = cursor[key]
            index_text = bracket[:-1]
            if not index_text.isdigit() or not isinstance(cursor, list):
                return None
            index = int(index_text)
            if index >= len(cursor):
                return None
            cursor = cursor[index]
            part = ""
        if not part:
            continue
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        elif isinstance(cursor, list) and part.isdigit() and int(part) < len(cursor):
            cursor = cursor[int(part)]
        else:
            return None
    return cursor


def _scope_claim_payload(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    return scope_claim_payload(
        payload,
        pointer_value,
        scope_claim_pointer=getattr(spec, "scope_claim_pointer", None),
    )


def _scope_expansion_gate_for_payload(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
) -> ScopeExpansionGate | None:
    return scope_expansion_gate_for_payload(
        payload,
        pointer_value,
        scope_claim_pointer=getattr(spec, "scope_claim_pointer", None),
        scope_evidence_pointer=getattr(spec, "scope_evidence_pointer", None),
    )


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


def _artifact_pointer(artifact: str, pointer: str | None) -> str | None:
    return f"{artifact}:{pointer}" if pointer is not None else None


def _readiness_pointer(ledger: GapHeadD5ReadinessLedger, name: str) -> str | None:
    for criterion in ledger.criteria:
        if criterion.name == name:
            return _artifact_pointer(criterion.artifact, criterion.pointer)
    return None


def _gap_head_d5_readiness(context: Mapping[str, Mapping[str, Any]]) -> GapHeadD5ReadinessLedger:
    return GapHeadOperationalReadinessPolicy().criteria(context)


def _gap_head_on_h_projection(
    payload: Mapping[str, Any],
    spec: CanonicalReportSpec,
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    evidence_pointer = "$.treatment_verdict.positive"
    context_payloads = {} if context is None else context
    ledger = _gap_head_d5_readiness(context_payloads)
    mechanism_namecert = context_payloads.get(ATTRIBUTION_CAPSULE_ARTIFACT, {})
    if pointer_value(payload, evidence_pointer) is True:
        overlay["positive_discovery"] = True
        overlay["net_positive_signal"] = True
        overlay["main_verdict"] = {
            "surface_delta_count": 1,
            "shift_information": 1,
            "structural_discovery": True,
        }
        overlay["evidence_basis"] = {"scorecard_ready": _scorecard_ready(context_payloads)}
        if ledger.all_pass:
            overlay["acceptance_gates"] = {"status": "pass"}
            overlay["final_status"] = "pass"
            ledger_debt = pointer_value(mechanism_namecert, MECHANISM_NAMECERT_LEDGER_POINTER)
            closure = pointer_value(mechanism_namecert, MECHANISM_NAMECERT_CLOSURE_POINTER)
            candidate = pointer_value(mechanism_namecert, MECHANISM_NAMECERT_CANDIDATE_POINTER)
            overlay["mechanism_attribution"] = {
                "all_pass": ledger_debt == "closed" and closure == "closed",
                "status": "ready" if ledger_debt == "closed" and closure == "closed" else "blocked",
                "failed_gate": None if ledger_debt == "closed" and closure == "closed" else MECHANISM_NAMECERT_LEDGER_POINTER,
                "channel": candidate,
            }
            overlay["source_pointers"] = {
                "operational": _artifact_pointer(GAP_HEAD_ROBUSTNESS_ARTIFACT, "$.acceptance_gates.status"),
                "mechanism": f"{ATTRIBUTION_CAPSULE_ARTIFACT}:{MECHANISM_NAMECERT_LEDGER_POINTER}",
                "mechanism_case": f"{ATTRIBUTION_CAPSULE_ARTIFACT}:{MECHANISM_NAMECERT_CLOSURE_POINTER}",
            }
        return overlay, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=evidence_pointer,
            control_pointer=spec.control_pointer,
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
            robustness_pointer=_readiness_pointer(ledger, "threshold"),
            adversarial_pointer=_readiness_pointer(ledger, "adversarial"),
            observed_debt_transfer_pointer=_readiness_pointer(ledger, "observed_debt_transfer"),
            d5_readiness=ledger,
        )
    return overlay, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer=evidence_pointer,
        scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
        robustness_pointer=_readiness_pointer(ledger, "threshold"),
        adversarial_pointer=_readiness_pointer(ledger, "adversarial"),
        observed_debt_transfer_pointer=_readiness_pointer(ledger, "observed_debt_transfer"),
        d5_readiness=ledger,
    )


def _gap_head_discovery_projection(
    payload: Mapping[str, Any],
    spec: CanonicalReportSpec,
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    context_payloads = {} if context is None else context
    if pointer_value(payload, "$.positive_discovery") is True:
        return {
            "net_positive_signal": True,
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
            },
            "evidence_basis": {"scorecard_ready": _scorecard_ready(context_payloads)},
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.positive_discovery",
            control_pointer=spec.control_pointer,
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
        )
    return {}, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer="$.positive_discovery",
        scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
    )


def _gap_head_robustness_projection(
    payload: Mapping[str, Any],
    spec: CanonicalReportSpec,
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    if pointer_value(payload, "$.acceptance_gates.status") == "pass" and pointer_value(payload, "$.final_status") == "pass":
        overlay["positive_discovery"] = True
        overlay["net_positive_signal"] = True
        overlay["main_verdict"] = {
            "surface_delta_count": 1,
            "shift_information": 1,
            "structural_discovery": True,
        }
        overlay["evidence_basis"] = {"scorecard_ready": _scorecard_ready({} if context is None else context)}
        return overlay, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.acceptance_gates.status",
            control_pointer=spec.control_pointer,
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
        )
    return overlay, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer="$.acceptance_gates.status",
        scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
    )


def _certificate_training_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    overlay: dict[str, Any] = {}
    status = pointer_value(payload, "$.result.status")
    capsule_terminal_verdict = pointer_value(payload, "$.claim_capsule.terminal_verdict")
    evidence_label = pointer_value(payload, "$.arm_protocol.compat_roles.after")
    debt_delta = _after_minus_before_debt_delta(payload)
    if isinstance(capsule_terminal_verdict, str) and capsule_terminal_verdict:
        overlay["verdict"] = capsule_terminal_verdict
    elif status == "negative":
        overlay["verdict"] = "rejected"
    if debt_delta is not None:
        overlay["main_verdict"] = {"deltas": {"debt_delta": debt_delta}}
    if pointer_value(payload, "$.claim_gate.audit_improvement_tradeoff") is True:
        overlay["claim_gate"] = {"training_audit_improvement_tradeoff": True}
    if status == "negative":
        return overlay, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.arm_protocol.compat_roles.after",
            evidence_label=evidence_label if isinstance(evidence_label, str) else None,
            failed_gate="$.claim_capsule.terminal_verdict",
            debt_row_pointer="$.deltas.after_minus_before.debt_delta",
        )
    if debt_delta is not None or pointer_value(payload, "$.claim_gate.audit_improvement_tradeoff") is True:
        return overlay, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.arm_protocol.compat_roles.after",
            evidence_label=evidence_label if isinstance(evidence_label, str) else None,
            debt_row_pointer="$.deltas.after_minus_before.debt_delta",
        )
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


def _sigreg_mini_grid_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    consistent, _reason, failed_pointer = _sigreg_mini_grid_consistency(payload)
    signal = pointer_value(payload, "$.discovery_map_signal")
    if not isinstance(signal, Mapping):
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.discovery_map_signal",
        )
    level = signal.get("level_candidate")
    status = signal.get("status")
    if consistent and level == "D2" and status == "d2-candidate":
        return {
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "sigreg_mini_grid": {
                    "level_candidate": "D2",
                    "status": "d2-candidate",
                    "evidence_pointer": "$.trend_summary.expected_trend",
                },
            },
            "evidence_basis": {
                "sigreg_mini_grid": True,
                "control_positive_discovery": None,
            },
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.trend_summary.expected_trend",
        )
    if consistent and level == "D1" and status == "d1-grid-evidence":
        return {
            "main_verdict": {
                "deltas": {"debt_delta": -1.0},
                "sigreg_mini_grid": {
                    "level_candidate": "D1",
                    "status": "d1-grid-evidence",
                    "debt_row_pointer": "$.tradeoff_ledger.rows.0",
                },
            },
            "claim_gate": {"training_audit_improvement_tradeoff": True},
        }, ProjectionEvidence(
            projection_status="projected",
            debt_row_pointer="$.tradeoff_ledger.rows.0",
        )
    return {
        "verdict": "rejected",
        "main_verdict": {
            "sigreg_mini_grid": {
                "level_candidate": "DN",
                "status": "negative",
            },
        },
    }, ProjectionEvidence(
        projection_status="projected",
        failed_gate=failed_pointer,
    )


def _discovery_regularized_training_projection(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    consistent, _reason, failed_pointer = _discovery_regularized_training_consistency(payload)
    signal = pointer_value(payload, "$.discovery_map_signal")
    if not isinstance(signal, Mapping):
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.discovery_map_signal",
        )
    level = signal.get("level_candidate")
    status = signal.get("status")
    extension_failed_pointer = _drt_extension_failed_pointer(payload)
    context_payloads = {} if context is None else context
    if extension_failed_pointer is None and consistent and level == "D5-M" and status == "d5-m-candidate":
        if not _mechanism_dna_row_ready("discovery-regularized-training", context_payloads):
            return {
                "verdict": "rejected",
                "main_verdict": {
                    "discovery_regularized_training": {
                        "level_candidate": "DN",
                        "status": "negative",
                    },
                },
            }, ProjectionEvidence(
                projection_status="projected",
                failed_gate="$.training_mechanism_cert.status",
            )
    if extension_failed_pointer is None and consistent and level in {"D4", "D5-M"} and status in {"d4-candidate", "d5-m-candidate"}:
        return {
            "positive_discovery": True,
            "net_positive_signal": True,
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
                "discovery_regularized_training": {
                    "level_candidate": level,
                    "status": status,
                    "evidence_pointer": "$.training_mechanism_cert" if level == "D5-M" else "$.torch_training_evidence",
                    "torch_training_evidence_pointer": "$.torch_training_evidence",
                    "training_mechanism_cert_pointer": "$.training_mechanism_cert",
                    "jet_loss_surface_pointer": "$.jet_loss_surface",
                    "jet_sidecar_pointer": "$.jet_sidecar_artifacts.owner_pointer",
                },
            },
            "training_mechanism_cert": pointer_value(payload, "$.training_mechanism_cert"),
            "mechanism_attribution": {
                "all_pass": level == "D5-M",
                "status": "ready" if level == "D5-M" else "candidate",
                "failed_gate": None if level == "D5-M" else "$.hardgate.gates.DRT-HG8.status",
                "channel": "training-mechanism-cert",
            },
            "source_pointers": {
                "operational": "$.torch_training_evidence",
                "mechanism": "$.training_mechanism_cert",
                "mechanism_case": "$.mechanism_ablation",
            },
            **(
                {"acceptance_gates": {"status": "pass"}, "final_status": "pass"}
                if level == "D5-M"
                else {}
            ),
            "evidence_basis": {
                "discovery_regularized_training": True,
                "control_positive_discovery": False,
                "net_positive_signal": True,
                "scorecard_ready": _scorecard_ready(context_payloads),
                "audit_status": "pass",
            },
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.training_mechanism_cert" if level == "D5-M" else "$.torch_training_evidence",
            control_pointer="$.matched_random_control",
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
        )
    return {
        "verdict": "rejected",
        "main_verdict": {
            "discovery_regularized_training": {
                "level_candidate": "DN",
                "status": "negative",
            },
        },
    }, ProjectionEvidence(
        projection_status="projected",
        failed_gate=extension_failed_pointer or failed_pointer,
    )


def _mechanism_seeking_network_projection(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    consistent, _reason, failed_pointer = _mechanism_seeking_network_consistency(payload)
    signal = pointer_value(payload, "$.discovery_map_signal")
    if not isinstance(signal, Mapping):
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.discovery_map_signal",
        )
    level = signal.get("level_candidate")
    status = signal.get("status")
    if consistent and level == "D4" and status == "d4-candidate":
        return {
            "positive_discovery": True,
            "net_positive_signal": True,
            "mechanism_attribution": {
                "all_pass": pointer_value(payload, "$.d5_m_readiness.status") == "ready",
                "status": pointer_value(payload, "$.d5_m_readiness.status"),
                "failed_gate": pointer_value(payload, "$.d5_m_readiness.failed_gate"),
                "channel": "distinction-module",
            },
            "source_pointers": {
                "operational": "$.source_artifacts.d5_o_source",
                "mechanism": "$.distinction_module_evidence",
                "mechanism_case": "$.hardgate.gates.MSN-HG6",
            },
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
                "mechanism_seeking_network": {
                    "level_candidate": "D4",
                    "status": "d4-candidate",
                    "evidence_pointer": "$.mechanism_gate_summary",
                    "mechanism_evidence_pointer": "$.distinction_module_evidence",
                    "d5_m_readiness_pointer": "$.d5_m_readiness",
                },
            },
            "evidence_basis": {
                "mechanism_seeking_network": True,
                "control_positive_discovery": False,
                "net_positive_signal": True,
                "scorecard_ready": _scorecard_ready({} if context is None else context),
            },
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.mechanism_gate_summary",
            control_pointer="$.matched_random_control",
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
        )
    return {
        "verdict": "rejected",
        "main_verdict": {
            "mechanism_seeking_network": {
                "level_candidate": "DN",
                "status": "negative",
            },
        },
    }, ProjectionEvidence(
        projection_status="projected",
        failed_gate=failed_pointer,
    )


def _certificate_gated_attention_projection(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    consistent, _reason, failed_pointer = _certificate_gated_attention_consistency(payload)
    signal = pointer_value(payload, "$.discovery_map_signal")
    if not isinstance(signal, Mapping):
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.discovery_map_signal",
        )
    level = signal.get("level_candidate")
    status = signal.get("status")
    if consistent and level == "D4" and status == "d4-candidate":
        return {
            "positive_discovery": True,
            "net_positive_signal": True,
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
                "certificate_gated_attention": {
                    "level_candidate": "D4",
                    "status": "d4-candidate",
                    "evidence_pointer": "$.certificate_gate_summary.gated_vs_plain_valid",
                    "route_patch_protocol_pointer": "$.route_patch_protocol",
                    "entropy_only_control_pointer": "$.route_patch_protocol.entropy_only_control",
                    "certificate_evidence_pointer": "$.certificate_gate_summary",
                    "torch_attention_evidence_pointer": "$.torch_attention_evidence",
                },
            },
            "evidence_basis": {
                "certificate_gated_attention": True,
                "control_positive_discovery": False,
                "net_positive_signal": True,
                "scorecard_ready": _scorecard_ready({} if context is None else context),
            },
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer="$.certificate_gate_summary.gated_vs_plain_valid",
            control_pointer="$.route_patch_protocol",
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
        )
    return {
        "verdict": "rejected",
        "main_verdict": {
            "certificate_gated_attention": {
                "level_candidate": "DN",
                "status": "negative",
            },
        },
    }, ProjectionEvidence(
        projection_status="projected",
        failed_gate=failed_pointer,
    )


def _dgt_terminal_d4_accepted(context: Mapping[str, Mapping[str, Any]]) -> bool:
    rows = context.get(HIGH_IMPACT_REVIEW_ARTIFACT, {}).get("review_rows")
    if not isinstance(rows, list):
        return False
    return any(
        isinstance(row, Mapping)
        and row.get("claim_id") == "claim:discovery-gated-transformer"
        and row.get("status") == "pass"
        and row.get("reason") == POSITIVE_DISCOVERY_GATES_PASS_REASON
        for row in rows
    )


def _discovery_gated_transformer_consistency(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[bool, str, str]:
    projection = pointer_value(payload, "$.d4_projection")
    if not isinstance(projection, Mapping):
        return False, "missing-dgt-d4-projection", "$.d4_projection"
    gates = projection.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != {f"PROJ-HG{index}" for index in range(1, 11)}:
        return False, "dgt-d4-projection-gates-mismatch", "$.d4_projection.gates"
    failed = next(
        (
            name
            for name in (f"PROJ-HG{index}" for index in range(1, 11))
            if not isinstance(gates.get(name), Mapping) or gates[name].get("status") != "pass"
        ),
        None,
    )
    expected_level = "D4" if failed is None else "D0"
    if projection.get("discovery_level") != expected_level:
        return False, "dgt-d4-projection-level-mismatch", "$.d4_projection.discovery_level"
    if projection.get("failed_gate") != failed:
        return False, "dgt-d4-projection-failed-gate-mismatch", "$.d4_projection.failed_gate"
    if projection.get("net_positive_signal") is not True:
        return False, "dgt-d4-net-positive-missing", "$.d4_projection.net_positive_signal"
    delta_pointer = projection.get("classifier_surface_delta_pointer")
    if not isinstance(delta_pointer, str) or pointer_value(payload, delta_pointer) is None:
        return False, "dgt-d4-classifier-delta-pointer-unresolved", "$.d4_projection.classifier_surface_delta_pointer"
    audit = projection.get("forbidden_claim_term_audit")
    if not isinstance(audit, Mapping) or audit.get("status") != "pass":
        return False, "dgt-d4-forbidden-claim-audit-failed", "$.d4_projection.forbidden_claim_term_audit"
    not_claimed = projection.get("not_claimed")
    not_claimed_text = " ".join(str(item).lower() for item in not_claimed) if isinstance(not_claimed, list) else ""
    if not not_claimed_text or "global superiority" in not_claimed_text or "production" in not_claimed_text:
        return False, "dgt-d4-not-claimed-boundary-failed", "$.d4_projection.not_claimed"
    if _has_terminal_verdict_key(payload):
        return False, "dgt-terminal-verdict-forbidden", "$"
    return True, "", "$.d4_projection.failed_gate" if failed is not None else "$.d4_projection.discovery_level"


def _has_terminal_verdict_key(value: Any) -> bool:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if key == "terminal_verdict" or _has_terminal_verdict_key(item):
                return True
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return any(_has_terminal_verdict_key(item) for item in value)
    return False


def _dgt_d5_o_projection_status(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[bool, str, str]:
    del context
    projection = pointer_value(payload, "$.d5_o_projection")
    if not isinstance(projection, Mapping):
        return False, "missing-dgt-d5-o-projection", "$.d5_o_projection"
    gates = projection.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != {f"D5O-HG{index}" for index in range(1, 9)}:
        return False, "dgt-d5-o-gates-mismatch", "$.d5_o_projection.gates"
    for gate_name in (f"D5O-HG{index}" for index in range(1, 9)):
        gate = gates.get(gate_name)
        if not isinstance(gate, Mapping) or gate.get("status") != "pass":
            return False, f"dgt-d5-o-blocked-by-{gate_name}", f"$.d5_o_projection.gates.{gate_name}"
        evidence = gate.get("evidence")
        if not isinstance(evidence, Mapping):
            return False, f"dgt-d5-o-unresolved-{gate_name}", f"$.d5_o_projection.gates.{gate_name}"
        artifact = evidence.get("artifact")
        local_pointer = evidence.get("pointer")
        if artifact != DISCOVERY_GATED_TRANSFORMER_ARTIFACT:
            if not isinstance(artifact, str) or not isinstance(local_pointer, str) or not local_pointer.startswith("$."):
                return False, f"dgt-d5-o-unresolved-{gate_name}", f"$.d5_o_projection.gates.{gate_name}"
            continue
        if isinstance(local_pointer, str) and local_pointer.startswith("$.") and pointer_value(payload, local_pointer) is None:
            return False, f"dgt-d5-o-unresolved-{gate_name}", f"$.d5_o_projection.gates.{gate_name}"
    if projection.get("gate_status") != "pass" or projection.get("status") != "ready":
        return False, "dgt-d5-o-status-not-ready", "$.d5_o_projection.status"
    if projection.get("discovery_level") != "D5-O":
        return False, "dgt-d5-o-level-mismatch", "$.d5_o_projection.discovery_level"
    return True, "", "$.d5_o_projection"


def _dgt_d5_m_projection_status(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    projection = pointer_value(payload, "$.d5_m_projection")
    if not isinstance(projection, Mapping):
        return False, "missing-dgt-d5-m-projection", "$.d5_m_projection"
    gates = projection.get("hardgates")
    if not isinstance(gates, Mapping) or set(gates) != {f"D5M-HG{index}" for index in range(1, 11)}:
        return False, "dgt-d5-m-gates-mismatch", "$.d5_m_projection.hardgates"
    for gate_name in (f"D5M-HG{index}" for index in range(1, 11)):
        gate = gates.get(gate_name)
        if not isinstance(gate, Mapping) or gate.get("status") != "pass":
            return False, f"dgt-d5-m-blocked-by-{gate_name}", f"$.d5_m_projection.hardgates.{gate_name}"
        evidence = gate.get("evidence")
        if not isinstance(evidence, Mapping):
            return False, f"dgt-d5-m-unresolved-{gate_name}", f"$.d5_m_projection.hardgates.{gate_name}"
        artifact = evidence.get("artifact")
        local_pointer = evidence.get("pointer")
        if artifact != DISCOVERY_GATED_TRANSFORMER_ARTIFACT:
            return False, f"dgt-d5-m-external-evidence-{gate_name}", f"$.d5_m_projection.hardgates.{gate_name}"
        if not isinstance(local_pointer, str) or not local_pointer.startswith("$.") or pointer_value(payload, local_pointer) is None:
            return False, f"dgt-d5-m-unresolved-{gate_name}", f"$.d5_m_projection.hardgates.{gate_name}"
    if projection.get("gate_status") != "pass" or projection.get("status") != "ready":
        return False, "dgt-d5-m-status-not-ready", "$.d5_m_projection.status"
    if projection.get("discovery_level") != "D5-M":
        return False, "dgt-d5-m-level-mismatch", "$.d5_m_projection.discovery_level"
    if projection.get("evidence_scope") != ["bounded-design", "toy-model", "theorem-backed", "production-forbidden"]:
        return False, "dgt-d5-m-scope-mismatch", "$.d5_m_projection.evidence_scope"
    if projection.get("terminal_verdict_scope") != "Core":
        return False, "dgt-d5-m-terminal-scope-mismatch", "$.d5_m_projection.terminal_verdict_scope"
    return True, "", "$.d5_m_projection"


def _dgt_scaling_ladder_projection_status(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    ladder = pointer_value(payload, "$.scaling_ladder")
    if not isinstance(ladder, Mapping):
        return False, "missing-dgt_scaling_ladder_owner", "$.scaling_ladder"
    hardgate = ladder.get("hardgate")
    if not isinstance(hardgate, Mapping):
        return False, "dgt_scaling_ladder_owner-hardgate-missing", "$.scaling_ladder.hardgate"
    gates = hardgate.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != {f"SCALE-HG{index}" for index in range(1, 7)}:
        return False, "dgt_scaling_ladder_owner-gates-mismatch", "$.scaling_ladder.hardgate.gates"
    for gate_name in (f"SCALE-HG{index}" for index in range(1, 7)):
        gate = gates.get(gate_name)
        if not isinstance(gate, Mapping) or gate.get("status") != "pass":
            return False, f"dgt_scaling_ladder_owner-blocked-by-{gate_name}", f"$.scaling_ladder.hardgate.gates.{gate_name}"
        evidence = gate.get("evidence")
        if not isinstance(evidence, Mapping):
            return False, f"dgt_scaling_ladder_owner-unresolved-{gate_name}", f"$.scaling_ladder.hardgate.gates.{gate_name}"
        if evidence.get("artifact") != DISCOVERY_GATED_TRANSFORMER_ARTIFACT:
            return False, f"dgt_scaling_ladder_owner-external-evidence-{gate_name}", f"$.scaling_ladder.hardgate.gates.{gate_name}"
        local_pointer = evidence.get("pointer")
        if not isinstance(local_pointer, str) or not local_pointer.startswith("$.") or pointer_value(payload, local_pointer) is None:
            return False, f"dgt_scaling_ladder_owner-unresolved-{gate_name}", f"$.scaling_ladder.hardgate.gates.{gate_name}"
    if ladder.get("status") != "ready" or hardgate.get("status") != "pass":
        return False, "dgt_scaling_ladder_owner-status-not-ready", "$.scaling_ladder.status"
    if ladder.get("discovery_level") != "D5-M":
        return False, "dgt_scaling_ladder_owner-level-mismatch", "$.scaling_ladder.discovery_level"
    if ladder.get("evidence_scope") != "bounded-model-prototype-scaling":
        return False, "dgt_scaling_ladder_owner-scope-mismatch", "$.scaling_ladder.evidence_scope"
    return True, "", "$.scaling_ladder"


def _dgt_scaling_owner_context(context: Mapping[str, Mapping[str, Any]] | None) -> Mapping[str, Any]:
    context_payloads = {} if context is None else context
    return context_payloads.get(SCALING_LADDER_ARTIFACT, {})


def _dgt_scaling_owner_level(
    context: Mapping[str, Mapping[str, Any]] | None,
    *,
    level_id: str = "L0_toy",
) -> tuple[Mapping[str, Any] | None, int | None]:
    owner = _dgt_scaling_owner_context(context)
    levels = owner.get("levels") if isinstance(owner, Mapping) else None
    if not isinstance(levels, Sequence) or isinstance(levels, (str, bytes, bytearray)):
        return None, None
    for index, row in enumerate(levels):
        if isinstance(row, Mapping) and row.get("level_id") == level_id:
            return row, index
    return None, None


def _dgt_scaling_owner_pointer(index: int | None) -> str:
    return f"{SCALING_LADDER_ARTIFACT}:$.levels[{0 if index is None else index}]"


def _dgt_scaling_owner_status(
    context: Mapping[str, Mapping[str, Any]] | None,
    *,
    level_id: str = "L0_toy",
) -> tuple[bool, str, str, Mapping[str, Any] | None]:
    row, index = _dgt_scaling_owner_level(context, level_id=level_id)
    pointer = _dgt_scaling_owner_pointer(index)
    if row is None:
        return False, "scaling-ladder-owner-missing", pointer, None
    state = row.get("state")
    reason = row.get("reason")
    if state != "open":
        return False, f"scaling-ladder-owner-{state or 'missing'}:{reason or 'missing-reason'}", pointer, row
    owner = _dgt_scaling_owner_context(context)
    hardgates = owner.get("hardgates") if isinstance(owner, Mapping) else None
    if not isinstance(hardgates, Mapping):
        return False, "scaling-ladder-owner-hardgates-missing", f"{SCALING_LADDER_ARTIFACT}:$.hardgates", row
    for gate_id, gate in hardgates.items():
        if not isinstance(gate, Mapping) or gate.get("status") != "pass":
            return False, f"scaling-ladder-owner-hardgate-failed:{gate_id}", f"{SCALING_LADDER_ARTIFACT}:$.hardgates.{gate_id}", row
    return True, "", pointer, row


def _discovery_gated_transformer_projection(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    consistent, _reason, failed_pointer = _discovery_gated_transformer_consistency(payload, context)
    projection = pointer_value(payload, "$.d4_projection")
    projection = projection if isinstance(projection, Mapping) else {}
    level = projection.get("discovery_level")
    owner_open, owner_reason, owner_pointer, owner_row = _dgt_scaling_owner_status(context)
    if owner_row is None:
        return {
            "positive_discovery": False,
            "net_positive_signal": False,
            "main_verdict": {
                "surface_delta_count": 0,
                "shift_information": 0,
                "structural_discovery": False,
                "discovery_gated_transformer": {
                    "level_candidate": "D0",
                    "status": "scaling-ladder-missing",
                },
            },
        }, ProjectionEvidence(
            projection_status="source-insufficient",
            evidence_pointer=owner_pointer,
            failed_gate=owner_pointer,
        )
    if not owner_open:
        return {
            "positive_discovery": False,
            "net_positive_signal": False,
            "main_verdict": {
                "surface_delta_count": 0,
                "shift_information": 0,
                "structural_discovery": False,
                "discovery_gated_transformer": {
                    "level_candidate": "D0",
                    "status": "scaling-ladder-owner-blocked",
                    "blocked_reason": owner_reason,
                    "evidence_pointer": owner_pointer,
                },
            },
        }, ProjectionEvidence(
            projection_status="source-insufficient",
            evidence_pointer=owner_pointer,
            failed_gate=owner_pointer,
        )
    if consistent and level == "D4":
        dgt_level = "D4"
        evidence_pointer = owner_pointer
        return {
            "positive_discovery": True,
            "net_positive_signal": True,
            "main_verdict": {
                "positive_discovery": True,
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
                "discovery_gated_transformer": {
                    "level_candidate": dgt_level,
                    "status": "scaling-ladder-owner-open",
                    "evidence_pointer": evidence_pointer,
                    "blocked_reason": None,
                    "classifier_surface_delta_pointer": "$.tool_route_evidence.classifier_surface_delta",
                },
            },
            "matched_random_control": {"control_positive": False},
            "evidence_basis": {
                "discovery_gated_transformer": True,
                "control_positive_discovery": False,
                "net_positive_signal": True,
                "scorecard_ready": True,
                "audit_status": "pass",
            },
            "scope_seal": pointer_value(payload, "$.d4_projection.scope_seal"),
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=evidence_pointer,
            control_pointer="$.d4_projection.matched_control",
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
            failed_gate=None,
        )
    return {
        "verdict": "rejected",
        "main_verdict": {
            "discovery_gated_transformer": {
                "level_candidate": "D0",
                "status": "blocked",
            },
        },
    }, ProjectionEvidence(
        projection_status="source-insufficient",
        failed_gate=failed_pointer,
    )


def _ledger_aware_transformer_consistency(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    signal = pointer_value(payload, "$.discovery_map_signal")
    hardgates = pointer_value(payload, "$.hardgate.gates")
    failed_gate = pointer_value(payload, "$.hardgate.failed_gate")
    robustness = pointer_value(payload, "$.robustness_signal")
    parameter_matched = pointer_value(payload, "$.parameter_matched_baseline")
    compute_matched = pointer_value(payload, "$.compute_matched_baseline")
    mechanism_certificate = pointer_value(payload, "$.mechanism_certificate")
    if not isinstance(signal, Mapping):
        return False, "missing-lat-discovery-map-signal", "$.discovery_map_signal"
    if not isinstance(hardgates, Mapping) or not hardgates:
        return False, "missing-lat-hardgates", "$.hardgate.gates"
    if not isinstance(robustness, Mapping):
        return False, "missing-lat-robustness-signal", "$.robustness_signal"
    if not isinstance(parameter_matched, Mapping):
        return False, "missing-lat-parameter-matched-baseline", "$.parameter_matched_baseline"
    if not isinstance(compute_matched, Mapping):
        return False, "missing-lat-compute-matched-baseline", "$.compute_matched_baseline"
    if not isinstance(mechanism_certificate, Mapping):
        return False, "missing-lat-mechanism-certificate", "$.mechanism_certificate"
    failed = next(
        (
            name
            for name in ("LAT-HG1", "LAT-HG2", "LAT-HG3", "LAT-HG4", "LAT-HG5", "LAT-HG6", "LAT-HG7", "LAT-HG8")
            if not isinstance(hardgates.get(name), Mapping) or hardgates[name].get("status") != "pass"
        ),
        None,
    )
    if failed != failed_gate:
        return False, "lat-hardgate-failed_gate-mismatch", "$.hardgate.failed_gate"
    if failed is None and robustness.get("status") != "pass":
        return False, "lat-robustness-signal-failed", "$.robustness_signal.status"
    effective_failed = failed
    expected = {
        "status": "d5-o-candidate" if effective_failed is None else "negative",
        "level_candidate": "D5-O" if effective_failed is None else "DN",
        "reason": "lat-hardgates-pass" if effective_failed is None else "hardgate-failed",
        "failed_gate": effective_failed,
        "failed_gate_pointer": None if effective_failed is None else f"$.hardgate.gates.{effective_failed}.status",
    }
    for key, expected_value in expected.items():
        if signal.get(key) != expected_value:
            pointer = signal.get("failed_gate_pointer")
            return False, f"lat-{key}-mismatch", pointer if isinstance(pointer, str) else "$.discovery_map_signal"
    for key in (
        "evidence_pointer",
        "control_pointer",
        "scorecard_pointer",
        "torch_training_evidence_pointer",
        "robustness_evidence_pointer",
        "parameter_matched_baseline_pointer",
        "compute_matched_baseline_pointer",
        "mechanism_certificate_pointer",
    ):
        pointer = signal.get(key)
        if not isinstance(pointer, str):
            return False, f"lat-missing-{key.replace('_', '-')}", "$.discovery_map_signal"
        if pointer_value(payload, pointer) is None:
            return False, f"lat-dangling-{key.replace('_', '-')}", pointer
    if signal.get("robustness_evidence_pointer") != "$.robustness_signal":
        return False, "lat-robustness-pointer-mismatch", "$.discovery_map_signal.robustness_evidence_pointer"
    if signal.get("parameter_matched_baseline_pointer") != "$.parameter_matched_baseline":
        return False, "lat-parameter-matched-pointer-mismatch", "$.discovery_map_signal.parameter_matched_baseline_pointer"
    if pointer_value(payload, "$.discovery_map_signal.parameter_matched_baseline_pointer") is None:
        return False, "lat-parameter-matched-pointer-dangling", "$.discovery_map_signal.parameter_matched_baseline_pointer"
    if signal.get("compute_matched_baseline_pointer") != "$.compute_matched_baseline":
        return False, "lat-compute-matched-pointer-mismatch", "$.discovery_map_signal.compute_matched_baseline_pointer"
    if pointer_value(payload, "$.discovery_map_signal.compute_matched_baseline_pointer") is None:
        return False, "lat-compute-matched-pointer-dangling", "$.discovery_map_signal.compute_matched_baseline_pointer"
    if signal.get("mechanism_certificate_pointer") != "$.mechanism_certificate":
        return False, "lat-mechanism-certificate-pointer-mismatch", "$.discovery_map_signal.mechanism_certificate_pointer"
    if pointer_value(payload, "$.discovery_map_signal.mechanism_certificate_pointer") is None:
        return False, "lat-mechanism-certificate-pointer-dangling", "$.discovery_map_signal.mechanism_certificate_pointer"
    if failed is None and mechanism_certificate.get("status") != "pass":
        return False, "lat-mechanism-certificate-failed", "$.mechanism_certificate.status"
    positive_claim = pointer_value(payload, "$.positive_claim")
    positive_claim_mechanism_pointer = (
        positive_claim.get("mechanism_certificate_pointer")
        if isinstance(positive_claim, Mapping)
        else None
    )
    if not isinstance(positive_claim_mechanism_pointer, str) or pointer_value(payload, positive_claim_mechanism_pointer) != mechanism_certificate:
        return False, "lat-positive-claim-mechanism-pointer-dangling", "$.positive_claim.mechanism_certificate_pointer"
    if pointer_value(payload, "$.claim_capsule_ref.capsule") is None:
        return False, "lat-claim-capsule-pointer-dangling", "$.claim_capsule_ref.pointer"
    if pointer_value(payload, "$.forbidden_claim_term_audit.status") != "pass":
        return False, "lat-forbidden-claim-term-audit-failed", "$.forbidden_claim_term_audit.status"
    if pointer_value(payload, "$.torch_training_evidence.protocol") is None:
        return False, "lat-torch-protocol-missing", "$.torch_training_evidence.protocol"
    return True, "", expected["failed_gate_pointer"] if isinstance(expected["failed_gate_pointer"], str) else "$.robustness_signal"


def _ledger_aware_transformer_projection(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    consistent, _reason, failed_pointer = _ledger_aware_transformer_consistency(payload)
    signal = pointer_value(payload, "$.discovery_map_signal")
    if not isinstance(signal, Mapping):
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            failed_gate="$.discovery_map_signal",
        )
    if consistent and signal.get("level_candidate") == "D5-O" and signal.get("status") == "d5-o-candidate":
        return {
            "positive_discovery": True,
            "net_positive_signal": True,
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
                "ledger_aware_transformer": {
                    "level_candidate": "D5-O",
                    "status": "d5-o-candidate",
                    "evidence_pointer": signal.get("evidence_pointer"),
                    "torch_training_evidence_pointer": signal.get("torch_training_evidence_pointer"),
                    "robustness_evidence_pointer": signal.get("robustness_evidence_pointer"),
                    "mechanism_certificate_pointer": signal.get("mechanism_certificate_pointer"),
                },
            },
            "evidence_basis": {
                "ledger_aware_transformer": True,
                "control_positive_discovery": False,
                "net_positive_signal": True,
                "robustness_ready": True,
                "scorecard_ready": _scorecard_ready({} if context is None else context),
            },
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=signal.get("evidence_pointer") if isinstance(signal.get("evidence_pointer"), str) else None,
            control_pointer=signal.get("control_pointer") if isinstance(signal.get("control_pointer"), str) else None,
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
            robustness_pointer=f"{LEDGER_AWARE_TRANSFORMER_ARTIFACT}:$.robustness_signal",
        )
    return {
        "verdict": "rejected",
        "main_verdict": {
            "ledger_aware_transformer": {
                "level_candidate": "DN",
                "status": "negative",
            },
        },
    }, ProjectionEvidence(
        projection_status="projected",
        failed_gate=failed_pointer,
    )


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


def _sigreg_mini_grid_consistency(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    hardgates = pointer_value(payload, "$.c3_hardgates")
    signal = pointer_value(payload, "$.discovery_map_signal")
    if not isinstance(hardgates, Mapping) or not hardgates:
        return False, "missing-c3-hardgates", "$.c3_hardgates"
    if not isinstance(signal, Mapping):
        return False, "missing-discovery-map-signal", "$.discovery_map_signal"
    failed_gates = [
        name
        for name in ("C3-HG1", "C3-HG2", "C3-HG3", "C3-HG4")
        if not isinstance(hardgates.get(name), Mapping) or hardgates[name].get("status") != "pass"
    ]
    structural_failed = next((name for name in failed_gates if name in {"C3-HG1", "C3-HG2", "C3-HG4"}), None)
    if structural_failed is not None:
        expected = {
            "status": "negative",
            "level_candidate": "DN",
            "reason": "structural-hardgate-failed",
            "failed_gate": structural_failed,
            "failed_gate_pointer": f"$.c3_hardgates.{structural_failed}.status",
        }
    elif "C3-HG3" in failed_gates:
        expected = {
            "status": "d1-grid-evidence",
            "level_candidate": "D1",
            "reason": "trend-hardgate-failed",
            "failed_gate": "C3-HG3",
            "failed_gate_pointer": "$.c3_hardgates.C3-HG3.status",
        }
    else:
        expected = {
            "status": "d2-candidate",
            "level_candidate": "D2",
            "reason": "expected-trend",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }
    for key, expected_value in expected.items():
        if signal.get(key) != expected_value:
            pointer = signal.get("failed_gate_pointer")
            return False, f"sigreg-mini-grid-{key}-mismatch", pointer if isinstance(pointer, str) else "$.discovery_map_signal"
    if pointer_value(payload, "$.hardgate.failed_gate") != expected["failed_gate"]:
        return False, "sigreg-mini-grid-hardgate-failed_gate-mismatch", "$.hardgate.failed_gate"
    return True, "", expected["failed_gate_pointer"] if isinstance(expected["failed_gate_pointer"], str) else "$.hardgate.status"


def _drt_extension_failed_pointer(payload: Mapping[str, Any]) -> str | None:
    hardgates = pointer_value(payload, "$.drt_extension_hardgates")
    if not isinstance(hardgates, Mapping):
        return "$.drt_extension_hardgates"
    if hardgates.get("status") == "pass":
        return None
    pointer = hardgates.get("failed_gate_pointer")
    return pointer if isinstance(pointer, str) and pointer else "$.drt_extension_hardgates.status"


def _drt_cert_pointers_resolve(payload: Mapping[str, Any]) -> bool:
    cert = pointer_value(payload, "$.training_mechanism_cert")
    if not isinstance(cert, Mapping) or cert.get("status") != "pass":
        return False
    required = cert.get("required_pointers")
    if not isinstance(required, list) or not required:
        return False
    prefix = f"{DISCOVERY_REGULARIZED_TRAINING_ARTIFACT}:"
    for row in required:
        if not isinstance(row, Mapping) or row.get("status") != "pass":
            return False
        cell = row.get("pointer")
        if not isinstance(cell, str) or not cell.startswith(prefix):
            return False
        if pointer_value(payload, cell[len(prefix) :]) is None:
            return False
    for key in (
        "status_pointer",
        "mechanism_ablation_status_pointer",
        "torch_delta_pointer",
        "matched_control_pointer",
        "ledger_pointer",
        "negative_witness_pointer",
    ):
        cell = cert.get(key)
        if not isinstance(cell, str) or not cell.startswith(prefix):
            return False
        if pointer_value(payload, cell[len(prefix) :]) is None:
            return False
    return True


def _drt_jet_pointers_resolve(payload: Mapping[str, Any]) -> bool:
    sidecars = pointer_value(payload, "$.jet_sidecar_artifacts")
    surface = pointer_value(payload, "$.jet_loss_surface")
    protocol = pointer_value(payload, "$.jet_loss_protocol")
    if not all(isinstance(section, Mapping) for section in (sidecars, surface, protocol)):
        return False
    required = (
        "$.jet_sidecar_artifacts.owner_pointer",
        "$.jet_loss_surface.protocol_pointer",
        "$.jet_loss_surface.records_pointer",
        "$.jet_loss_surface.classifier_surface_delta_pointer",
        "$.jet_ablation.protocol_pointer",
        "$.jet_loss_frontier.protocol_pointer",
        "$.jet_loss_frontier.required_order_gain_pointer",
    )
    for pointer_cell in required:
        pointer = pointer_value(payload, pointer_cell)
        if not isinstance(pointer, str):
            return False
        if pointer.startswith(DISCOVERY_REGULARIZED_TRAINING_ARTIFACT + ":"):
            pointer = pointer[len(DISCOVERY_REGULARIZED_TRAINING_ARTIFACT) + 1 :]
        if pointer_value(payload, pointer) is None:
            return False
    return (
        surface.get("net_positive_signal") is True
        and pointer_value(payload, "$.torch_training_evidence.classifier_surface_delta.drt_minus_matched_random_classifier_shift_count") is not None
    )


def _discovery_regularized_training_consistency(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    hardgates = pointer_value(payload, "$.hardgate.gates")
    signal = pointer_value(payload, "$.discovery_map_signal")
    if not isinstance(hardgates, Mapping) or not hardgates:
        return False, "missing-drt-hardgates", "$.hardgate.gates"
    if not isinstance(signal, Mapping):
        return False, "missing-drt-discovery-map-signal", "$.discovery_map_signal"
    failed = next(
        (
            name
            for name in ("DRT-HG1", "DRT-HG2", "DRT-HG3", "DRT-HG4", "DRT-HG5", "DRT-HG6", "DRT-HG7")
            if not isinstance(hardgates.get(name), Mapping) or hardgates[name].get("status") != "pass"
        ),
        None,
    )
    torch_evidence = pointer_value(payload, "$.torch_training_evidence")
    if failed is None:
        if not isinstance(torch_evidence, Mapping):
            failed = "DRT-HG6"
        elif torch_evidence.get("status") != "available":
            failed = "DRT-HG6"
        elif not isinstance(torch_evidence.get("row_count"), int) or int(torch_evidence["row_count"]) <= 0:
            failed = "DRT-HG6"
        elif torch_evidence.get("row_count") != torch_evidence.get("expected_row_count"):
            failed = "DRT-HG6"
        elif pointer_value(payload, "$.torch_training_evidence.protocols.0") is None:
            failed = "DRT-HG6"
        elif pointer_value(payload, "$.records.raw_rows_pointer") is None:
            failed = "DRT-HG6"
    if failed is None and pointer_value(payload, "$.mechanism_ablation.status") != "pass":
        failed = "DRT-HG7"
    if failed is None and not _drt_jet_pointers_resolve(payload):
        failed = "DRTJ-HG1"
    cert = pointer_value(payload, "$.training_mechanism_cert")
    cert_present = isinstance(cert, Mapping)
    cert_ready = _drt_cert_pointers_resolve(payload)
    promotion_gate_present = cert_present or "DRT-HG8" in hardgates
    promotion_failed = failed is None and promotion_gate_present and not cert_ready
    if failed is None and "DRT-HG8" in hardgates:
        hg8 = hardgates.get("DRT-HG8")
        if not isinstance(hg8, Mapping) or hg8.get("status") != ("pass" if cert_ready else "fail"):
            return False, "drt-hg8-status-mismatch", "$.hardgate.gates.DRT-HG8.status"
    extension_failed_pointer = _drt_extension_failed_pointer(payload)
    if failed is None and cert_ready:
        expected = {
            "status": "d5-m-candidate",
            "level_candidate": "D5-M",
            "reason": "training-mechanism-certificate-positive",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }
    elif promotion_failed:
        expected = {
            "status": "d4-candidate",
            "level_candidate": "D4",
            "reason": "mechanism-certificate-promotion-failed",
            "failed_gate": "DRT-HG8",
            "failed_gate_pointer": "$.hardgate.gates.DRT-HG8.status",
        }
    elif failed is None:
        expected = {
            "status": "d4-candidate",
            "level_candidate": "D4",
            "reason": "matched-control-positive",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }
    else:
        expected = {
            "status": "negative",
            "level_candidate": "DN",
            "reason": "hardgate-failed",
            "failed_gate": failed,
            "failed_gate_pointer": f"$.hardgate.gates.{failed}.status",
        }
    for key, expected_value in expected.items():
        if signal.get(key) != expected_value:
            pointer = signal.get("failed_gate_pointer")
            return False, f"drt-{key}-mismatch", pointer if isinstance(pointer, str) else "$.discovery_map_signal"
    if pointer_value(payload, "$.hardgate.failed_gate") != expected["failed_gate"]:
        return False, "drt-hardgate-failed_gate-mismatch", "$.hardgate.failed_gate"
    if signal.get("torch_training_evidence_pointer") != "$.torch_training_evidence":
        return False, "drt-torch-pointer-mismatch", "$.discovery_map_signal.torch_training_evidence_pointer"
    if pointer_value(payload, "$.discovery_map_signal.torch_training_evidence_pointer") is None:
        return False, "drt-torch-pointer-dangling", "$.discovery_map_signal.torch_training_evidence_pointer"
    if signal.get("level_candidate") == "D5-M":
        if signal.get("training_mechanism_cert_pointer") != "$.training_mechanism_cert":
            return False, "drt-training-cert-pointer-mismatch", "$.discovery_map_signal.training_mechanism_cert_pointer"
        if not cert_ready:
            return False, "drt-d5-m-without-training-cert", "$.training_mechanism_cert.status"
    if extension_failed_pointer is not None and pointer_value(payload, extension_failed_pointer) is None:
        return False, "drt-extension-failed-gate-pointer-dangling", extension_failed_pointer
    if extension_failed_pointer is not None:
        return True, "", extension_failed_pointer
    return True, "", expected["failed_gate_pointer"] if isinstance(expected["failed_gate_pointer"], str) else "$.torch_training_evidence"


def _mechanism_seeking_network_consistency(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    signal = pointer_value(payload, "$.discovery_map_signal")
    hardgate = pointer_value(payload, "$.hardgate.gates")
    failed = pointer_value(payload, "$.hardgate.failed_gate")
    forbidden_audit = pointer_value(payload, "$.forbidden_claim_term_audit.status")
    mechanism_summary = pointer_value(payload, "$.mechanism_gate_summary")
    module_evidence = pointer_value(payload, "$.distinction_module_evidence")
    readiness = pointer_value(payload, "$.d5_m_readiness")
    if not isinstance(signal, Mapping):
        return False, "missing-msn-discovery-map-signal", "$.discovery_map_signal"
    if not isinstance(hardgate, Mapping):
        return False, "missing-msn-hardgates", "$.hardgate.gates"
    if not isinstance(mechanism_summary, Mapping):
        return False, "missing-msn-mechanism-gate-summary", "$.mechanism_gate_summary"
    by_mechanism = mechanism_summary.get("by_mechanism")
    if not isinstance(by_mechanism, Mapping) or not by_mechanism:
        return False, "missing-msn-by-mechanism", "$.mechanism_gate_summary.by_mechanism"
    accepted_surface_count = sum(1 for row in by_mechanism.values() if isinstance(row, Mapping) and row.get("accepted") is True)
    if mechanism_summary.get("accepted_surface_count") != accepted_surface_count:
        return False, "msn-accepted-surface-count-mismatch", "$.mechanism_gate_summary.accepted_surface_count"
    expected_accepted = accepted_surface_count >= 3
    if mechanism_summary.get("accepted") is not expected_accepted:
        return False, "msn-accepted-flag-mismatch", "$.mechanism_gate_summary.accepted"
    expected_hg2 = "pass" if expected_accepted else "fail"
    if pointer_value(payload, "$.hardgate.gates.MSN-HG2.status") != expected_hg2:
        return False, "msn-hg2-status-mismatch", "$.hardgate.gates.MSN-HG2.status"
    if accepted_surface_count < 3 and signal.get("level_candidate") in {"D4", "D5-M"}:
        return False, "msn-positive-signal-without-surface-floor", "$.discovery_map_signal.level_candidate"
    if not isinstance(module_evidence, Mapping):
        return False, "missing-msn-distinction-module-evidence", "$.distinction_module_evidence"
    if not isinstance(readiness, Mapping):
        return False, "missing-msn-d5-m-readiness", "$.d5_m_readiness"
    if module_evidence.get("owner_pointer") != "$.distinction_module_evidence":
        return False, "msn-distinction-owner-pointer-mismatch", "$.distinction_module_evidence.owner_pointer"
    module_records = module_evidence.get("records")
    if not isinstance(module_records, list) or not module_records:
        return False, "missing-msn-distinction-module-records", "$.distinction_module_evidence.records"
    for index, record in enumerate(module_records):
        if not isinstance(record, Mapping):
            return False, "invalid-msn-distinction-module-record", f"$.distinction_module_evidence.records[{index}]"
        for field in (
            "tensor_slice_pointer",
            "classifier_surface_pointer",
            "stability_score_pointer",
            "shortcut_risk_pointer",
            "ledger_risk_pointer",
            "ablation_rows_pointer",
            "patch_rows_pointer",
        ):
            pointer = record.get(field)
            if not isinstance(pointer, str) or pointer_value(payload, pointer) is None:
                return False, f"msn-distinction-{field}-dangling", f"$.distinction_module_evidence.records[{index}].{field}"
    hg6_status = pointer_value(payload, "$.hardgate.gates.MSN-HG6.status")
    accepted_modules = [
        module_id
        for module_id, row in by_mechanism.items()
        if isinstance(row, Mapping) and row.get("accepted") is True
    ]
    accepted_records = [
        record
        for record in module_records
        if isinstance(record, Mapping) and record.get("module_id") in accepted_modules
    ]
    expected_hg6 = "pass" if accepted_modules and len(accepted_records) == len(accepted_modules) and all(
        record.get("ablation_status") == "pass"
        and record.get("patch_status") == "pass"
        and record.get("risk_audit_status") == "pass"
        and record.get("audit_status") == "pass"
        for record in accepted_records
    ) else "fail"
    if hg6_status != expected_hg6:
        return False, "msn-hg6-status-mismatch", "$.hardgate.gates.MSN-HG6.status"
    source_present = isinstance(pointer_value(payload, "$.source_artifacts.d5_o_source"), str) and bool(pointer_value(payload, "$.source_artifacts.d5_o_source"))
    expected_readiness = "ready" if expected_hg6 == "pass" and source_present else "blocked"
    if readiness.get("status") != expected_readiness:
        return False, "msn-d5-m-readiness-status-mismatch", "$.d5_m_readiness.status"
    if readiness.get("passed") is not (expected_readiness == "ready"):
        return False, "msn-d5-m-readiness-passed-mismatch", "$.d5_m_readiness.passed"
    if readiness.get("distinction_module_evidence_ref") != "$.distinction_module_evidence":
        return False, "msn-d5-m-readiness-evidence-ref-mismatch", "$.d5_m_readiness.distinction_module_evidence_ref"
    evidence_ref = pointer_value(payload, "$.d5_m_readiness.distinction_module_evidence_ref")
    if not isinstance(evidence_ref, str) or pointer_value(payload, evidence_ref) is None:
        return False, "msn-d5-m-readiness-evidence-ref-dangling", "$.d5_m_readiness.distinction_module_evidence_ref"
    if expected_readiness != "ready" and signal.get("level_candidate") == "D5-M":
        return False, "msn-d5-m-projection-without-readiness", "$.discovery_map_signal.level_candidate"
    failed_gates = [
        name
        for name, row in hardgate.items()
        if isinstance(name, str) and name.startswith("MSN-HG") and (not isinstance(row, Mapping) or row.get("status") != "pass")
    ]
    all_pass = not failed_gates and forbidden_audit == "pass"
    if all_pass:
        expected = {
            "status": "d4-candidate",
            "level_candidate": "D4",
            "reason": "mechanism-gate-positive",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }
    else:
        expected_failed = failed_gates[0] if failed_gates else "forbidden-positive-claim-term"
        expected = {
            "status": "negative",
            "level_candidate": "DN",
            "reason": "hardgate-failed" if failed_gates else "forbidden-positive-claim-term",
            "failed_gate": expected_failed,
            "failed_gate_pointer": f"$.hardgate.gates.{expected_failed}.status" if failed_gates else "$.forbidden_claim_term_audit.status",
        }
    for key, expected_value in expected.items():
        if signal.get(key) != expected_value:
            pointer = signal.get("failed_gate_pointer")
            return False, f"msn-{key}-mismatch", pointer if isinstance(pointer, str) else "$.discovery_map_signal"
    if pointer_value(payload, "$.hardgate.failed_gate") != expected["failed_gate"]:
        return False, "msn-hardgate-failed_gate-mismatch", "$.hardgate.failed_gate"
    if signal.get("surface_registry_pointer") != "$.surface_registry":
        return False, "msn-surface-registry-pointer-mismatch", "$.discovery_map_signal.surface_registry_pointer"
    if signal.get("mechanism_evidence_pointer") != "$.mechanism_gate_summary.by_mechanism":
        return False, "msn-mechanism-pointer-mismatch", "$.discovery_map_signal.mechanism_evidence_pointer"
    if pointer_value(payload, "$.discovery_map_signal.surface_registry_pointer") is None:
        return False, "msn-surface-registry-pointer-dangling", "$.discovery_map_signal.surface_registry_pointer"
    if pointer_value(payload, "$.discovery_map_signal.mechanism_evidence_pointer") is None:
        return False, "msn-mechanism-pointer-dangling", "$.discovery_map_signal.mechanism_evidence_pointer"
    return True, "", expected["failed_gate_pointer"] if isinstance(expected["failed_gate_pointer"], str) else "$.mechanism_gate_summary"


def _certificate_gated_attention_consistency(payload: Mapping[str, Any]) -> tuple[bool, str, str]:
    hardgates = pointer_value(payload, "$.hardgate.gates")
    signal = pointer_value(payload, "$.discovery_map_signal")
    route_patch = pointer_value(payload, "$.route_patch_protocol")
    entropy_control = pointer_value(payload, "$.route_patch_protocol.entropy_only_control")
    not_claimed = pointer_value(payload, "$.not_claimed")
    if not isinstance(hardgates, Mapping) or not hardgates:
        return False, "missing-cga-hardgates", "$.hardgate.gates"
    if not isinstance(signal, Mapping):
        return False, "missing-cga-discovery-map-signal", "$.discovery_map_signal"
    for name in ("CGA-HG1", "CGA-HG2", "CGA-HG3", "CGA-HG4", "CGA-HG5", "CGA-HG6"):
        if name not in hardgates:
            return False, f"missing-{name.lower()}", f"$.hardgate.gates.{name}.status"
    if not isinstance(route_patch, Mapping):
        return False, "missing-cga-route-patch-protocol", "$.route_patch_protocol"
    if not isinstance(entropy_control, Mapping):
        return False, "missing-cga-entropy-only-control", "$.route_patch_protocol.entropy_only_control"
    if not isinstance(not_claimed, list):
        return False, "missing-cga-not-claimed", "$.not_claimed"
    if any(item not in not_claimed for item in REQUIRED_PRODUCTION_NOT_CLAIMED):
        return False, "missing-cga-production-boundary", "$.not_claimed"
    if not isinstance(hardgates["CGA-HG6"], Mapping) or hardgates["CGA-HG6"].get("evidence_pointer") != "$.not_claimed":
        return False, "cga-production-boundary-pointer-mismatch", "$.hardgate.gates.CGA-HG6.evidence_pointer"
    failed = next(
        (
            name
            for name in ("CGA-HG1", "CGA-HG2", "CGA-HG3", "CGA-HG4", "CGA-HG5", "CGA-HG6")
            if not isinstance(hardgates.get(name), Mapping) or hardgates[name].get("status") != "pass"
        ),
        None,
    )
    if failed is None:
        expected = {
            "status": "d4-candidate",
            "level_candidate": "D4",
            "reason": "certificate-gate-positive",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }
    else:
        expected = {
            "status": "negative",
            "level_candidate": "DN",
            "reason": "hardgate-failed",
            "failed_gate": failed,
            "failed_gate_pointer": f"$.hardgate.gates.{failed}.status",
        }
    for key, expected_value in expected.items():
        if signal.get(key) != expected_value:
            pointer = signal.get("failed_gate_pointer")
            return False, f"cga-{key}-mismatch", pointer if isinstance(pointer, str) else "$.discovery_map_signal"
    if pointer_value(payload, "$.hardgate.failed_gate") != expected["failed_gate"]:
        return False, "cga-hardgate-failed_gate-mismatch", "$.hardgate.failed_gate"
    if expected["failed_gate"] is None and signal.get("control_pointer") != "$.route_patch_protocol":
        return False, "cga-control-pointer-mismatch", "$.discovery_map_signal.control_pointer"
    if expected["failed_gate"] is None and signal.get("entropy_only_control_pointer") != "$.route_patch_protocol.entropy_only_control":
        return False, "cga-entropy-only-control-pointer-mismatch", "$.discovery_map_signal.entropy_only_control_pointer"
    if expected["failed_gate"] is None and pointer_value(payload, "$.discovery_map_signal.control_pointer") is None:
        return False, "cga-missing-control-pointer-cell", "$.discovery_map_signal.control_pointer"
    if expected["failed_gate"] is None and pointer_value(payload, "$.discovery_map_signal.entropy_only_control_pointer") is None:
        return False, "cga-missing-entropy-only-control-pointer-cell", "$.discovery_map_signal.entropy_only_control_pointer"
    if signal.get("certificate_evidence_pointer") != "$.certificate_gate_summary":
        return False, "cga-certificate-pointer-mismatch", "$.discovery_map_signal.certificate_evidence_pointer"
    if signal.get("torch_attention_evidence_pointer") != "$.torch_attention_evidence":
        return False, "cga-torch-pointer-mismatch", "$.discovery_map_signal.torch_attention_evidence_pointer"
    return True, "", expected["failed_gate_pointer"] if isinstance(expected["failed_gate_pointer"], str) else "$.certificate_gate_summary.gated_vs_plain_valid"


def _derivative_atlas_failed_gate_pointer(payload: Mapping[str, Any]) -> str | None:
    failed_gate = pointer_value(payload, "$.failed_gate")
    if isinstance(failed_gate, str) and failed_gate:
        layer_pointer = f"$.hardgates.by_layer.{failed_gate}.status"
        if pointer_value(payload, layer_pointer) is not None:
            return layer_pointer
        gate_pointer = f"$.hardgates.{failed_gate}.status"
        if pointer_value(payload, gate_pointer) is not None:
            return gate_pointer
        if pointer_value(payload, "$.hardgates.status") is not None:
            return "$.hardgates.status"
    if pointer_value(payload, "$.hardgates.status") == "fail":
        return "$.hardgates.status"
    if pointer_value(payload, "$.hardgate.status") == "fail":
        return "$.hardgate.status"
    return None


def _derivative_debt_row_pointer(payload: Mapping[str, Any]) -> str | None:
    gaps = _sequence_cell(pointer_value(payload, "$.ledger_gaps"))
    for index, row in enumerate(gaps):
        if isinstance(row, Mapping) and str(row.get("status") or "") in {"open", "partial", "fail"}:
            return f"$.ledger_gaps[{index}]"
    failed_gate = pointer_value(payload, "$.failed_gate")
    if isinstance(failed_gate, str) and failed_gate:
        index = _pointer_index(gaps, key="failed_gate", value=failed_gate)
        if index is not None:
            return f"$.ledger_gaps[{index}]"
    items = _sequence_cell(pointer_value(payload, "$.debt_items"))
    for index, row in enumerate(items):
        if isinstance(row, Mapping) and str(row.get("status") or "") in {"open", "partial", "fail"}:
            return f"$.debt_items[{index}]"
    return None


def _derivative_negative_projection(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ProjectionEvidence]:
    failed_pointer = _derivative_atlas_failed_gate_pointer(payload)
    debt_pointer = _derivative_debt_row_pointer(payload)
    if failed_pointer is None:
        return {}, ProjectionEvidence(projection_status="source-insufficient")
    return {
        "verdict": "rejected",
        "positive_discovery": False,
        "net_positive_signal": False,
        "main_verdict": {
            "derivative_debt": {
                "status": "negative",
                "level_candidate": "DN",
                "failed_gate_pointer": failed_pointer,
                "debt_row_pointer": debt_pointer,
            },
        },
    }, ProjectionEvidence(
        projection_status="projected",
        evidence_pointer="$.bounded_lab_evidence",
        failed_gate=failed_pointer,
        debt_row_pointer=debt_pointer,
    )


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


def _dimension_mismatch_projection(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
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
                canonical_terminal_verdict="negative_discovery",
            )
        if effective_level == "D4" and terminal_verdict == "source_pass":
            return {
                "positive_discovery": True,
                "net_positive_signal": True,
                "main_verdict": {
                    "surface_delta_count": 1,
                    "shift_information": 1,
                    "structural_discovery": True,
                },
                "evidence_basis": {
                    "control_positive_discovery": False,
                    "scorecard_ready": _scorecard_ready({} if context is None else context),
                },
                "audit_decision": {"audit_status": "pass"},
            }, ProjectionEvidence(
                projection_status="projected",
                evidence_pointer=DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER,
                canonical_terminal_verdict="source_pass",
                control_pointer="$.hardgate_evidence.HG-B3.matched_random_positive",
                scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
            )
        if anti_triviality_status == "scale_leakage_detected":
            return {"verdict": "rejected"}, ProjectionEvidence(
                projection_status="projected",
                evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
                failed_gate=DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER,
                canonical_terminal_verdict=terminal_verdict if isinstance(terminal_verdict, str) else None,
            )
    if status == "failed":
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
            failed_gate=DIMENSION_MISMATCH_TRANSFER_POINTER,
            canonical_terminal_verdict=terminal_verdict if isinstance(terminal_verdict, str) else None,
        )
    return {}, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer=DIMENSION_MISMATCH_TRANSFER_POINTER,
    )


def _gap_head_transfer_atlas_projection(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    decision = pointer_value(payload, GAP_HEAD_TRANSFER_ATLAS_DECISION_POINTER)
    if decision == "pass":
        return {
            "positive_discovery": True,
            "net_positive_signal": True,
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
            },
            "evidence_basis": {
                "control_positive_discovery": False,
                "scorecard_ready": _scorecard_ready({} if context is None else context),
            },
            "acceptance_gates": {"status": "pass"},
            "final_status": "pass",
        }, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=GAP_HEAD_TRANSFER_ATLAS_DECISION_POINTER,
            control_pointer=GAP_HEAD_TRANSFER_ATLAS_CONTROL_POINTER,
            scorecard_pointer=f"{QUALITY_SCORECARD_ARTIFACT}:{QUALITY_SCORECARD_ROWS_POINTER}",
        )
    if decision == "failed":
        return {"verdict": "rejected"}, ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=GAP_HEAD_TRANSFER_ATLAS_DECISION_POINTER,
            failed_gate=GAP_HEAD_TRANSFER_ATLAS_DECISION_POINTER,
        )
    return {}, ProjectionEvidence(
        projection_status="source-insufficient",
        evidence_pointer=GAP_HEAD_TRANSFER_ATLAS_DECISION_POINTER,
    )


def _attribution_capsule_levels(payload: Mapping[str, Any]) -> AttributionCapsuleLevels | None:
    evidence = project_gap_head_mechanism_evidence(payload)
    if evidence is None:
        return None
    mechanism_level = evidence.mechanism_level
    mechanism_status = evidence.mechanism_status
    channel = evidence.candidate_mechanism
    failed_gate = evidence.failed_gate
    if evidence.base_status == "ready" and mechanism_level == "blocked" and isinstance(failed_gate, str) and channel:
        return AttributionCapsuleLevels(
            base_level=evidence.base_level,
            evidence_level=evidence.evidence_level,
            base_status=evidence.base_status,
            mechanism_level="blocked",
            mechanism_status="blocked",
            mechanism_channel=channel,
            failed_gate=failed_gate,
            operational_pointer=ATTRIBUTION_CAPSULE_OPERATIONAL_POINTER,
            mechanism_pointer=ATTRIBUTION_CAPSULE_MECHANISM_POINTER,
            mechanism_case_pointer=ATTRIBUTION_CAPSULE_MECHANISM_CASE_POINTER,
            mechanism_namecert_pointer=ATTRIBUTION_CAPSULE_ARTIFACT,
            mechanism_ledger_pointer=f"{ATTRIBUTION_CAPSULE_ARTIFACT}:{evidence.ledger_debt_pointer}",
            mechanism_closure_pointer=f"{ATTRIBUTION_CAPSULE_ARTIFACT}:{evidence.closure_pointer}",
        )
    if evidence.base_status == "ready" and mechanism_level == "D5-M":
        return AttributionCapsuleLevels(
            base_level=evidence.base_level,
            evidence_level=evidence.evidence_level,
            base_status=evidence.base_status,
            mechanism_level="D5-M",
            mechanism_status="ready",
            mechanism_channel=channel,
            failed_gate=None,
            operational_pointer=ATTRIBUTION_CAPSULE_OPERATIONAL_POINTER,
            mechanism_pointer=ATTRIBUTION_CAPSULE_MECHANISM_POINTER,
            mechanism_case_pointer=ATTRIBUTION_CAPSULE_MECHANISM_CASE_POINTER,
            mechanism_namecert_pointer=ATTRIBUTION_CAPSULE_ARTIFACT,
            mechanism_ledger_pointer=f"{ATTRIBUTION_CAPSULE_ARTIFACT}:{evidence.ledger_debt_pointer}",
            mechanism_closure_pointer=f"{ATTRIBUTION_CAPSULE_ARTIFACT}:{evidence.closure_pointer}",
        )
    return None


def _source_audit_status(payload: Mapping[str, Any]) -> str | None:
    audit_decision = payload.get("audit_decision")
    if isinstance(audit_decision, Mapping) and isinstance(audit_decision.get("audit_status"), str):
        return audit_decision["audit_status"]
    if isinstance(payload.get("audit_status"), str):
        return payload["audit_status"]
    statuses: list[str] = []

    def collect(value: Any, path: tuple[str, ...] = ()) -> None:
        if isinstance(value, Mapping):
            audit_status = value.get("audit_status")
            if isinstance(audit_status, str):
                statuses.append(audit_status)
            status = value.get("status")
            if isinstance(status, str) and path and "audit" in path[-1]:
                statuses.append(status)
            for key, child in value.items():
                if isinstance(key, str):
                    collect(child, (*path, key))
        elif isinstance(value, list):
            for child in value:
                collect(child, path)

    collect(payload)
    if not statuses:
        return None
    for status in statuses:
        if status not in {"valid", "consistent", "pass"}:
            return status
    return "pass"


def _with_source_audit_status(overlay: dict[str, Any], payload: Mapping[str, Any]) -> dict[str, Any]:
    if overlay.get("positive_discovery") is not True:
        return overlay
    result = dict(overlay)
    audit_status = _source_audit_status(payload)
    if audit_status is None:
        return result
    basis = result.get("evidence_basis")
    compact_basis = dict(basis) if isinstance(basis, Mapping) else {}
    compact_basis["audit_status"] = audit_status
    result["evidence_basis"] = compact_basis
    return result


def _projection_overlay_and_evidence(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, Any], ProjectionEvidence]:
    if spec.name == "gap-head-on-h":
        overlay, evidence = _gap_head_on_h_projection(payload, spec, context)
    elif spec.name == "gap-head-discovery":
        overlay, evidence = _gap_head_discovery_projection(payload, spec, context)
    elif spec.name == "gap-head-robustness-sweep":
        overlay, evidence = _gap_head_robustness_projection(payload, spec, context)
    elif spec.name == "certificate-guided-training":
        overlay, evidence = _certificate_training_projection(payload)
    elif spec.name == "certificate-guided-discovery":
        overlay, evidence = _certificate_discovery_projection(payload)
    elif spec.name == "sigreg-training-proxy":
        overlay, evidence = _sigreg_training_proxy_projection(payload)
    elif spec.name == "sigreg-mini-grid":
        overlay, evidence = _sigreg_mini_grid_projection(payload)
    elif spec.name == "discovery-regularized-training":
        overlay, evidence = _discovery_regularized_training_projection(payload, context)
    elif spec.name == "mechanism-seeking-network":
        overlay, evidence = _mechanism_seeking_network_projection(payload, context)
    elif spec.name == "certificate-gated-attention":
        overlay, evidence = _certificate_gated_attention_projection(payload, context)
    elif spec.name == "discovery-gated-transformer":
        overlay, evidence = _discovery_gated_transformer_projection(payload, context)
    elif spec.name == "dgt-neural-ablation":
        passed = pointer_value(payload, "$.nabl_hardgates.status") == "pass"
        claim_count = len(payload.get("component_causal_claims", [])) if isinstance(payload.get("component_causal_claims"), list) else 0
        hardgates = payload.get("nabl_hardgates")
        failed_gate = hardgates.get("failed_gate") if isinstance(hardgates, Mapping) else None
        overlay, evidence = {
            "positive_discovery": bool(passed and claim_count),
            "main_verdict": {
                "positive_discovery": bool(passed and claim_count),
                "surface_delta_count": claim_count,
                "shift_information": float(claim_count),
                "net_information": float(claim_count),
            },
            "net_positive_signal": bool(passed and claim_count),
            "matched_random_control": {"control_positive": False},
            "evidence_basis": {
                "scorecard_ready": passed,
                "audit_status": "pass" if passed else "fail",
                "robustness_ready": passed,
            },
            "d5_m": {"status": "ready" if passed else "blocked", "passed": passed, "failed_gate": None if passed else failed_gate},
            "training_mechanism_cert": {"status": "pass" if passed else "fail"},
            "scope_seal": CLOSED_CLAIM_SCOPE_SEAL,
            "source_pointers": {
                "operational": "$.nabl_hardgates.status",
                "mechanism": "$.component_causal_claims",
                "mechanism_case": "$.claim_capsule_ref",
            },
        }, ProjectionEvidence(
            projection_status="dgt-neural-ablation-pointer-only",
            evidence_pointer="$.component_causal_claims",
            control_pointer="$.training_protocol",
            scorecard_pointer="$.nabl_hardgates.status",
        )
    elif spec.name == "transformer-derivative-atlas":
        overlay, evidence = _derivative_negative_projection(payload)
    elif spec.name == "ledger-aware-transformer":
        overlay, evidence = _ledger_aware_transformer_projection(payload, context)
    elif spec.name == "gap-head-ablation":
        overlay, evidence = _gap_head_ablation_projection(payload)
    elif spec.name == "gap-head-transfer-atlas":
        overlay, evidence = _gap_head_transfer_atlas_projection(payload, context)
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
            evidence_pointer=MECHANISM_EVIDENCE_POINTER,
        )
    elif spec.name == "lejepa-theorem-ledger":
        overlay, evidence = {}, ProjectionEvidence(
            projection_status="theorem-ledger-recorded",
            evidence_pointer="$.theorem_rows",
        )
    else:
        overlay, evidence = {}, ProjectionEvidence(projection_status="source-insufficient")
    if _scope_claim_payload(spec, payload) is not None and evidence.control_pointer is None:
        evidence = ProjectionEvidence(
            projection_status="projected",
            evidence_pointer=spec.positive_claim_pointer,
            evidence_label=evidence.evidence_label,
            control_pointer=spec.control_pointer,
            scorecard_pointer=spec.positive_claim_pointer,
            failed_gate=evidence.failed_gate,
            debt_row_pointer=evidence.debt_row_pointer,
            robustness_pointer=evidence.robustness_pointer,
            adversarial_pointer=evidence.adversarial_pointer,
            observed_debt_transfer_pointer=evidence.observed_debt_transfer_pointer,
            d5_readiness=evidence.d5_readiness,
            canonical_terminal_verdict=evidence.canonical_terminal_verdict,
        )
    overlay = _with_source_audit_status(overlay, payload)
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
            **dict(payload),
            "artifact_id": payload.get("artifact_id", spec.name),
            "json_artifact": payload.get("json_artifact", spec.json_artifact),
            **overlay,
        }
    projected = dict(payload)
    projected.update(overlay)
    gate = _scope_expansion_gate_for_payload(spec, payload)
    if gate is not None:
        projected["scope_gate"] = gate.as_dict()
        claim = _scope_claim_payload(spec, payload)
        if claim is not None:
            projected["scope_claim"] = dict(claim)
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


def _atlas_claim_terminal(payload: Mapping[str, Any], level: DiscoveryLevel) -> str:
    decision = pointer_value(payload, GAP_HEAD_TRANSFER_ATLAS_DECISION_POINTER)
    if decision == "failed" or level == "DN":
        return "rejected"
    if decision != "pass" or level not in {"D5-O", "D5-M"}:
        return ""
    return MECHANISM_NOT_CLOSED_CLAIM_VERDICT


def _atlas_claim_acceptance_consistent(payload: Mapping[str, Any], level: DiscoveryLevel, terminal_verdict: str) -> bool:
    derived = _atlas_claim_terminal(payload, level)
    if terminal_verdict == "pass":
        return derived == ACCEPTED_CLAIM_VERDICT
    return derived != ACCEPTED_CLAIM_VERDICT and terminal_verdict == derived


def _audit_pointer_cell(
    payload: Mapping[str, Any],
    pointer: str | None,
    missing_reason: str,
    unresolved_reason: str,
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[str, str] | None:
    if pointer is None:
        return "invalid", missing_reason
    context_payloads = {} if context is None else context
    value = _artifact_pointer_value(payload, pointer, context_payloads) if ":" in pointer else pointer_value(payload, pointer)
    if value is None:
        return "invalid", unresolved_reason
    return None


def _audit_emitted_pointers(payload: Mapping[str, Any], evidence: ProjectionEvidence) -> tuple[str, str] | None:
    for field in (
        "evidence_pointer",
        "control_pointer",
        "failed_gate",
        "debt_row_pointer",
        "robustness_pointer",
        "adversarial_pointer",
        "observed_debt_transfer_pointer",
    ):
        pointer = getattr(evidence, field)
        if pointer is not None and pointer_value(payload, pointer) is None:
            return "invalid", f"unresolved-{field.replace('_', '-')}"
    return None


def _artifact_pointer_value(
    payload: Mapping[str, Any],
    pointer: str | None,
    context: Mapping[str, Mapping[str, Any]],
) -> Any:
    if pointer is None:
        return None
    if ":" not in pointer:
        return pointer_value(payload, pointer)
    artifact, local_pointer = pointer.split(":", 1)
    return pointer_value(context.get(artifact, {}), local_pointer)


def _owner_local_anti_triviality_result(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    level: DiscoveryLevel,
) -> tuple[str, str] | None:
    if level not in {"D4", "D5-O", "D5-M"}:
        return None
    if payload.get("anti_triviality_status") not in {"pass", "anti_triviality_passed"}:
        return "invalid", "owner-anti-triviality-not-pass"
    if payload.get("anti_triviality_policy") != ANTI_TRIVIALITY_POLICY:
        return "invalid", "owner-anti-triviality-policy-mismatch"
    recommended = payload.get("anti_triviality_recommended_level")
    positive_rank = {"D4": 0, "D5-O": 1, "D5-M": 2}
    if recommended not in positive_rank or positive_rank[str(recommended)] < positive_rank[str(level)]:
        return "invalid", "owner-anti-triviality-level-mismatch"
    contract = payload.get("anti_triviality_gate_evidence")
    if not isinstance(contract, Mapping) or set(contract) != ANTI_TRIVIALITY_FAMILIES:
        return "invalid", "missing-owner-anti-triviality-contract"
    for family in ANTI_TRIVIALITY_FAMILIES:
        row = contract.get(family)
        if not isinstance(row, Mapping) or row.get("status") != "pass":
            return "invalid", f"owner-anti-triviality-{family}-not-pass"
        pointer = row.get("pointer")
        if not isinstance(pointer, str) or pointer_value(payload, pointer) is None:
            return "invalid", f"owner-anti-triviality-{family}-pointer-unresolved"
    return None


def _audit_spec_pointer_cells(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> tuple[str, str] | None:
    for field in ("scope_pointer", "cost_pointer", "not_claimed_pointer"):
        pointer = getattr(spec, field)
        if pointer is None:
            return "invalid", f"missing-{field.replace('_', '-')}"
        if pointer_value(payload, pointer) is None:
            return "invalid", f"unresolved-{field.replace('_', '-')}"
    if spec.control_pointer is None:
        if spec.no_control_rationale_pointer is None:
            return "invalid", "missing-no-control-rationale-pointer"
        if pointer_value(payload, spec.no_control_rationale_pointer) is None:
            return "invalid", "unresolved-no-control-rationale-pointer"
    elif spec.no_control_rationale_pointer is not None and pointer_value(payload, spec.no_control_rationale_pointer) is None:
        return "invalid", "unresolved-no-control-rationale-pointer"
    return None


def _audit_row(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    level: DiscoveryLevel,
    evidence: ProjectionEvidence,
    terminal_verdict: str = "",
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[str, str]:
    if level not in DISCOVERY_LEVELS:
        return "invalid", "missing-discovery-level"
    if spec.name == "gap-head-attribution-capsule":
        levels = _attribution_capsule_levels(payload)
        if levels is None:
            return "invalid", "attribution-capsule-level-cells-missing"
        mechanism_evidence = project_gap_head_mechanism_evidence(payload)
        if mechanism_evidence is None:
            return "invalid", "missing-mechanism-evidence"
        unresolved = unresolved_mechanism_evidence_pointers(payload, mechanism_evidence)
        if unresolved:
            return "invalid", "unresolved-mechanism-evidence-pointer"
        if levels.mechanism_level == "D5-M" and not mechanism_causal_evidence_ready(mechanism_evidence):
            return "invalid", "mechanism-causal-evidence-not-ready"
        if pointer_value(payload, levels.operational_pointer) is None:
            return "invalid", "unresolved-operational-pointer"
        if pointer_value(payload, levels.mechanism_pointer) is None:
            return "invalid", "unresolved-mechanism-pointer"
        if pointer_value(payload, levels.mechanism_case_pointer) is None:
            return "invalid", "unresolved-mechanism-case-pointer"
    spec_pointer_result = _audit_spec_pointer_cells(spec, payload)
    if spec_pointer_result is not None:
        return spec_pointer_result
    if spec.name == "gap-head-transfer-atlas":
        claim = pointer_value(payload, "$.multi_surface_d5_o")
        if not isinstance(claim, Mapping):
            return "invalid", "missing-atlas-claim"
        if pointer_value(payload, "$.forbidden_claim_term_audit.status") != "pass":
            return "invalid", "atlas-forbidden-claim-term-audit-failed"
        boundary_ledger = pointer_value(payload, "$.boundary_ledger")
        if not isinstance(boundary_ledger, list) or not boundary_ledger:
            return "invalid", "missing-atlas-boundary-ledger"
        if pointer_value(payload, "$.multi_surface_d5_o.decision") is None:
            return "invalid", "unresolved-atlas-decision"
        if pointer_value(payload, "$.multi_surface_d5_o.discovery_level") is None:
            return "invalid", "unresolved-atlas-discovery-level"
        pointer_result = _audit_emitted_pointers(payload, evidence)
        if pointer_result is not None:
            return pointer_result
        if not _atlas_claim_acceptance_consistent(payload, level, terminal_verdict):
            return "invalid", "atlas-terminal-claim-verdict-mismatch"
        return "valid", ""
    if spec.name == "sigreg-training-proxy":
        consistent, reason, _failed_pointer = _sigreg_training_proxy_consistency(payload)
        if not consistent:
            return "invalid", reason
    if spec.name == "sigreg-mini-grid":
        consistent, reason, _failed_pointer = _sigreg_mini_grid_consistency(payload)
        if not consistent:
            return "invalid", reason
    if spec.name == "discovery-regularized-training":
        consistent, reason, _failed_pointer = _discovery_regularized_training_consistency(payload)
        if not consistent:
            return "invalid", reason
    if spec.name == "mechanism-seeking-network":
        consistent, reason, _failed_pointer = _mechanism_seeking_network_consistency(payload)
        if not consistent:
            return "invalid", reason
    if spec.name == "certificate-gated-attention":
        consistent, reason, _failed_pointer = _certificate_gated_attention_consistency(payload)
        if not consistent:
            return "invalid", reason
    if spec.name == "discovery-gated-transformer":
        consistent, reason, _failed_pointer = _discovery_gated_transformer_consistency(payload, context)
        if not consistent:
            return "invalid", reason
        owner_open, owner_reason, _owner_pointer, _owner_row = _dgt_scaling_owner_status(context)
        if level in {"D4", "D5-O", "D5-M"} and not owner_open:
            return "invalid", owner_reason
        if level in {"D5-O", "D5-M"}:
            return "invalid", "scaling-ladder-owner-does-not-open-d5"
    if spec.name == "dgt-neural-ablation":
        if pointer_value(payload, "$.nabl_hardgates.status") != "pass":
            return "invalid", "dgt-neural-ablation-hardgate-failed"
        if not isinstance(pointer_value(payload, "$.component_causal_claims"), list):
            return "invalid", "dgt-neural-ablation-claims-missing"
        if pointer_value(payload, "$.claim_capsule_ref.artifact") is None:
            return "invalid", "dgt-neural-ablation-capsule-pointer-missing"
    if spec.name == "ledger-aware-transformer":
        consistent, reason, _failed_pointer = _ledger_aware_transformer_consistency(payload)
        if not consistent:
            return "invalid", reason
    if level in {"D4", "D5-O", "D5-M"}:
        if level in {"D5-O", "D5-M"} and spec.name == "gap-head-on-h":
            reason = _unresolved_d5_criterion(evidence, {} if context is None else context)
            if reason is not None:
                return "invalid", reason
        if spec.name != "discovery-gated-transformer":
            anti_result = _owner_local_anti_triviality_result(spec, payload, level)
            if anti_result is not None:
                return anti_result
        pointer_result = _audit_pointer_cell(
            payload,
            evidence.control_pointer,
            "missing-control-pointer",
            "unresolved-control-pointer",
        )
        if pointer_result is not None:
            return pointer_result
        context_payloads = {} if context is None else context
        if evidence.scorecard_pointer is None:
            return "invalid", "missing-scorecard-pointer"
        if _artifact_pointer_value(payload, evidence.scorecard_pointer, context_payloads) is None:
            return "invalid", "unresolved-scorecard-pointer"
    if level == "DN":
        pointer_result = _audit_pointer_cell(
            payload,
            evidence.failed_gate,
            "missing-failed-gate",
            "unresolved-failed-gate",
            {} if context is None else context,
        )
        if pointer_result is not None:
            return pointer_result
    if level == "D1":
        pointer_result = _audit_pointer_cell(
            payload,
            evidence.debt_row_pointer,
            "missing-debt-row-pointer",
            "unresolved-debt-row-pointer",
        )
        if pointer_result is not None:
            return pointer_result
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
    discovery_level: DiscoveryLevel = verdict.discovery_level
    terminal_verdict = verdict.terminal_verdict
    classifier_reasons = list(verdict.reasons)
    if spec.name == "discovery-gated-transformer":
        owner_open, owner_reason, _owner_pointer, _owner_row = _dgt_scaling_owner_status(context_payloads)
        if owner_open and discovery_level in {"D4", "D5-O", "D5-M"}:
            discovery_level = "D4"
            classifier_reasons = ["DGT scaling-ladder owner opened bounded D4 evidence"]
        else:
            discovery_level = "D0"
            terminal_verdict = ""
            classifier_reasons = [owner_reason or "DGT scaling-ladder owner blocked"]
    if spec.name == "gap-head-transfer-atlas":
        claim = pointer_value(payload, "$.multi_surface_d5_o")
        if isinstance(claim, Mapping) and claim.get("discovery_level") in DISCOVERY_LEVELS:
            terminal_verdict = _atlas_claim_terminal(payload, discovery_level)
    audit_status, audit_reason = _audit_row(spec, payload, discovery_level, evidence, terminal_verdict, context_payloads)
    if spec.name == "gap-head-transfer-atlas" and audit_status == "invalid":
        discovery_level = "DN"
        terminal_verdict = ""
    scope_claim = _scope_claim_payload(spec, payload)
    scope_gate = _scope_expansion_gate_for_payload(spec, payload)
    if scope_gate is not None and scope_gate.status == "fail" and (
        discovery_level in {"D4", "D5-O", "D5-M"}
        or "scope-expansion-evidence-missing" in classifier_reasons
    ):
        discovery_level = "DN"
        terminal_verdict = "negative_discovery"
        audit_status = "valid"
        audit_reason = scope_gate.reason
        classifier_reasons = [scope_gate.reason]
        evidence = ProjectionEvidence(
            projection_status=evidence.projection_status,
            evidence_pointer=evidence.evidence_pointer,
            evidence_label=evidence.evidence_label,
            control_pointer=evidence.control_pointer,
            scorecard_pointer=evidence.scorecard_pointer,
            failed_gate=scope_gate.failed_pointer or "$.scope_gate.failed_edge",
            debt_row_pointer=evidence.debt_row_pointer,
            robustness_pointer=evidence.robustness_pointer,
            adversarial_pointer=evidence.adversarial_pointer,
            observed_debt_transfer_pointer=evidence.observed_debt_transfer_pointer,
            d5_readiness=evidence.d5_readiness,
            canonical_terminal_verdict=evidence.canonical_terminal_verdict,
        )
    row: dict[str, Any] = {
        "report": spec.name,
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "discovery_level": discovery_level,
        "terminal_verdict": terminal_verdict,
        "classifier_reasons": classifier_reasons,
        "projection_status": evidence.projection_status,
        "evidence_pointer": evidence.evidence_pointer,
        "audit_status": audit_status,
        "audit_reason": audit_reason,
    }
    if evidence.control_pointer is not None:
        row["control_pointer"] = evidence.control_pointer
    if evidence.scorecard_pointer is not None:
        row["scorecard_pointer"] = evidence.scorecard_pointer
    if evidence.evidence_label is not None:
        row["evidence_label"] = evidence.evidence_label
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
    if spec.name == "discovery-gated-transformer":
        row["scaling_ladder_pointer"] = f"{SCALING_LADDER_ARTIFACT}:$.levels[0]"
    if scope_claim is not None:
        row["scope_claim"] = dict(scope_claim)
    if scope_gate is not None:
        row["scope_gate"] = scope_gate.as_dict()
    if spec.name == "gap-head-attribution-capsule":
        levels = _attribution_capsule_levels(payload)
        if levels is not None:
            row.update(
                {
                    "base_level": levels.base_level,
                    "mechanism_evidence_level": levels.evidence_level,
                    "mechanism_evidence_level_pointer": MECHANISM_EVIDENCE_LEVEL_POINTER,
                    "base_status": levels.base_status,
                    "mechanism_level": levels.mechanism_level,
                    "mechanism_status": levels.mechanism_status,
                    "mechanism_channel": levels.mechanism_channel,
                    "operational_pointer": levels.operational_pointer,
                    "mechanism_pointer": levels.mechanism_pointer,
                    "mechanism_case_pointer": levels.mechanism_case_pointer,
                    "mechanism_namecert_pointer": levels.mechanism_namecert_pointer,
                    "mechanism_ledger_pointer": levels.mechanism_ledger_pointer,
                    "mechanism_closure_pointer": levels.mechanism_closure_pointer,
                }
            )
            if levels.failed_gate is not None:
                row["mechanism_failed_gate"] = levels.failed_gate
    return row


def build_source_discovery_rows(
    *,
    root: Path | None = None,
    canonical_reports: Sequence[CanonicalReportSpec] | None = None,
    include_sidecars: bool = False,
) -> list[dict[str, Any]]:
    reports = CANONICAL_REPORTS if canonical_reports is None else canonical_reports
    gap_head_d5_context = _load_gap_head_d5_context(root=root)
    gap_head_d5_context[CLAIM_VERDICTS_ARTIFACT] = {"rows": _load_claim_verdict_rows(root=root)}
    scaling_ladder = _load_artifact_payload(SCALING_LADDER_ARTIFACT, root=root)
    if scaling_ladder:
        gap_head_d5_context[SCALING_LADDER_ARTIFACT] = scaling_ladder
    high_impact_review = _load_artifact_payload(HIGH_IMPACT_REVIEW_ARTIFACT, root=root)
    if high_impact_review:
        gap_head_d5_context[HIGH_IMPACT_REVIEW_ARTIFACT] = high_impact_review
    rows = [discovery_row(spec, _load_payload(spec, root=root), gap_head_d5_context) for spec in reports]
    dimension_payload = _load_artifact_payload(DIMENSION_MISMATCH_TRANSFER_ARTIFACT, root=root)
    if dimension_payload:
        rows.append(_dimension_mismatch_discovery_row(dimension_payload, gap_head_d5_context))
    if include_sidecars:
        rows.extend(_sidecar_discovery_rows(root=root))
    return rows


def _sidecar_discovery_rows(*, root: Path | None = None) -> list[dict[str, Any]]:
    base = _root(root)
    rows: list[dict[str, Any]] = []
    single = _load_artifact_payload(SINGLE_THRESHOLD_ESCAPE_ARTIFACT, root=base)
    if single:
        audit_status = "valid" if single.get("status") in {"escaped-positive-captured", "checked-fail-closed"} else "invalid"
        rows.append(
            {
                "report": "single-threshold-escape",
                "json_artifact": SINGLE_THRESHOLD_ESCAPE_ARTIFACT,
                "markdown_artifact": SINGLE_THRESHOLD_ESCAPE_MARKDOWN_ARTIFACT,
                "discovery_level": "DN",
                "terminal_verdict": "negative_discovery",
                "classifier_reasons": ["escaped-positive-is-not-discovery-evidence"],
                "projection_status": str(single.get("status") or ""),
                "evidence_pointer": "$.single_threshold_basis",
                "failed_gate": "$.projection.escaped_positive_is_discovery_evidence",
                "audit_status": audit_status,
                "audit_reason": "" if audit_status == "valid" else "single-threshold-sidecar-not-closed",
                "what_was_learned": "single-threshold escape evidence is gate failure evidence, not discovery evidence",
                "next_hypothesis": "replace threshold-only selection with control-matched multi-threshold evidence before any promotion attempt",
                "not_claimed": single.get("sidecar_not_claimed", []),
            }
        )
    training = _load_artifact_payload(TRAINING_CHOICE_OBSERVABILITY_ARTIFACT, root=base)
    if training:
        has_ledger_risk = pointer_value(training, "$.training_choice_observability.ledger_risk_only_arm_count")
        audit_status = "valid" if has_ledger_risk else "invalid"
        rows.append(
            {
                "report": "training-choice-observability",
                "json_artifact": TRAINING_CHOICE_OBSERVABILITY_ARTIFACT,
                "markdown_artifact": TRAINING_CHOICE_OBSERVABILITY_MARKDOWN_ARTIFACT,
                "discovery_level": "DN",
                "terminal_verdict": "negative_discovery",
                "classifier_reasons": ["training-choice-ledger-risk-only"],
                "projection_status": str(training.get("status") or ""),
                "evidence_pointer": "$.boundary_ledger",
                "failed_gate": "$.training_choice_observability.ledger_risk_only_arm_count",
                "audit_status": audit_status,
                "audit_reason": "" if audit_status == "valid" else "training-choice-ledger-risk-missing",
                "what_was_learned": "training choice remains ledger-risk-only rather than h-observable positive discovery",
                "next_hypothesis": "separate optimizer choice from training budget under matched protocol and forbidden-feature audit",
                "not_claimed": training.get("not_claimed", []),
            }
        )
    rows.extend(_gap_head_mechanism_blockage_rows(root=base))
    return rows


def _gap_head_mechanism_blockage_rows(*, root: Path) -> list[dict[str, Any]]:
    capsule = _load_artifact_payload(ATTRIBUTION_CAPSULE_ARTIFACT, root=root)
    evidence = project_gap_head_mechanism_evidence(capsule)
    if evidence is None:
        return []
    if (
        evidence.base_status != "ready"
        or evidence.mechanism_status != "blocked"
        or pointer_value(capsule, MECHANISM_NAMECERT_LEDGER_POINTER) != "open"
        or unresolved_mechanism_evidence_pointers(capsule, evidence)
    ):
        return []
    pointers = (
        MECHANISM_EVIDENCE_POINTER,
        "$.mechanism_evidence.failed_gate",
        evidence.ledger_debt_pointer,
    )
    if any(pointer_value(capsule, pointer) is None for pointer in pointers):
        return []
    not_claimed = pointer_value(capsule, "$.scope.not_claimed")
    if not isinstance(not_claimed, list):
        not_claimed = pointer_value(capsule, "$.not_claimed")
    if not isinstance(not_claimed, list):
        not_claimed = pointer_value(capsule, "$.scope_seal.not_claimed")
    if not isinstance(not_claimed, list):
        return []
    return [
        {
            "report": "gap-head-mechanism-blockage",
            "json_artifact": ATTRIBUTION_CAPSULE_ARTIFACT,
            "markdown_artifact": "reports/canonical/gap_head_attribution_capsule.md",
            "discovery_level": "DN",
            "terminal_verdict": "negative_discovery",
            "classifier_reasons": ["gap-head-mechanism-blocked"],
            "projection_status": "mechanism-blockage-projected",
            "evidence_pointer": MECHANISM_EVIDENCE_POINTER,
            "failed_gate": "$.mechanism_evidence.failed_gate",
            "debt_row_pointer": evidence.ledger_debt_pointer,
            "audit_status": "valid",
            "audit_reason": "",
            "what_was_learned": "gap-head operational readiness is present while D5-M remains blocked by the mechanism evidence",
            "next_hypothesis": "separate score and margin evidence from a closed mechanism proof before any D5-M promotion",
            "not_claimed": not_claimed,
        }
    ]


def build_negative_discovery_owner_rows(
    *,
    root: Path | None = None,
    canonical_reports: Sequence[CanonicalReportSpec] | None = None,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for source_row in build_source_discovery_rows(root=root, canonical_reports=canonical_reports, include_sidecars=True):
        if source_row.get("discovery_level") != "DN":
            continue
        report = str(source_row.get("report") or "")
        pointer = source_row.get("failed_gate") or source_row.get("debt_row_pointer") or source_row.get("evidence_pointer")
        artifact = str(source_row.get("json_artifact") or "")
        source = artifact if not isinstance(pointer, str) or not pointer else f"{artifact}:{pointer}"
        report_id = DIMENSION_MISMATCH_REPORT_ID if report == "dimension-mismatch-debt-transfer" else report
        row = {
            "negative_id": f"dn:{report_id}",
            "report_id": report_id,
            "claim_id": f"claim:{report}",
            "kind": "discovery_report",
            "report": report,
            "source": source,
            "json_artifact": artifact,
            "markdown_artifact": source_row.get("markdown_artifact"),
            "ledger_pointer": source,
            "discovery_level": "DN",
            "terminal_verdict": source_row.get("terminal_verdict"),
            "classifier_reasons": source_row.get("classifier_reasons", []),
            "projection_status": source_row.get("projection_status"),
            "evidence_pointer": source_row.get("evidence_pointer"),
            "failed_gate": source_row.get("failed_gate"),
            "debt_row_pointer": source_row.get("debt_row_pointer"),
            "audit_status": "pass" if source_row.get("audit_status") == "valid" else "fail",
            "audit_reason": source_row.get("audit_reason", ""),
        }
        for key in (
            "base_level",
            "anti_triviality_status",
            "downgrade_reason",
            "effective_level",
            "hypothesis",
            "next_hypothesis",
            "stop_reason",
            "not_claimed",
            "what_was_learned",
        ):
            if key in source_row:
                row[key] = source_row[key]
        if report_id == DIMENSION_MISMATCH_REPORT_ID:
            from scripts import run_dimension_mismatch_debt_transfer as dimension_transfer

            row["bedc_gap_mapping"] = dimension_transfer.scale_leakage_bedc_gap_mapping(_root(root))
        _fill_negative_report_boundary(row)
        rows.append(row)
    return rows


def _fill_negative_report_boundary(row: dict[str, Any]) -> None:
    report_id = str(row.get("report_id") or "")
    defaults = {
        "certificate-guided-training": {
            "what_was_learned": "constraint_lagrangian did not clear the audit-improvement hardgate",
            "next_hypothesis": "test whether a debt-only or constrained optimizer separates audit improvement from hidden classifier tradeoff",
        },
        "gap-head-ablation": {
            "what_was_learned": "removing the learned gap head breaks the projected discovery gate",
            "next_hypothesis": "isolate which gap-head channel carries the rejected ablation surface",
        },
        "spectral-ablation-hinge": {
            "what_was_learned": "spectral ablation does not beat the negative control boundary",
            "next_hypothesis": "replace the hinge with a control-matched spectral channel before any promotion attempt",
        },
        "certificate-guided-discovery": {
            "what_was_learned": "certificate-guided discovery remains negative at the canonical positive-discovery gate",
            "next_hypothesis": "reuse the training owner report and isolate whether any discovery surface survives matched controls",
        },
        DIMENSION_MISMATCH_REPORT_ID: {
            "next_hypothesis": "add anti-triviality evidence that rules out scale-only or metadata proxy separation",
        },
    }
    values = defaults.get(report_id, {})
    for key, value in values.items():
        row.setdefault(key, value)
    if not row.get("failed_gate"):
        row["failed_gate"] = "$"
    row.setdefault("what_was_learned", "DN projection records a source-boundary failure for this canonical artifact")
    row.setdefault("next_hypothesis", "inspect the source artifact before treating this DN row as a stable research packet")
    row.setdefault("stop_reason", None)


def _negative_index_by_report(
    source_rows: Sequence[Mapping[str, Any]],
    *,
    root: Path | None = None,
) -> dict[str, int]:
    owner_payload = _load_artifact_payload(NEGATIVE_DISCOVERY_REPORTS_ARTIFACT, root=root)
    owner_rows = owner_payload.get("rows") if isinstance(owner_payload, Mapping) else None
    if isinstance(owner_rows, list):
        owner_result: dict[str, int] = {}
        for index, row in enumerate(owner_rows):
            if isinstance(row, Mapping) and isinstance(row.get("report"), str):
                owner_result[str(row["report"])] = index
        if owner_result:
            return owner_result
    result: dict[str, int] = {}
    index = 0
    for row in source_rows:
        if row.get("discovery_level") != "DN":
            continue
        report = row.get("report")
        if isinstance(report, str) and report:
            result[report] = index
        index += 1
    return result


def _discovery_map_row(source_row: Mapping[str, Any], negative_indices: Mapping[str, int]) -> dict[str, Any]:
    row = dict(source_row)
    if row.get("discovery_level") != "DN":
        return row
    report = str(row.get("report") or "")
    pointer_index = negative_indices.get(report)
    pointer = None if pointer_index is None else f"{NEGATIVE_DISCOVERY_REPORTS_ARTIFACT}:$.rows[{pointer_index}]"
    return {
        key: value
        for key, value in row.items()
        if key not in DN_FACT_KEYS
    } | {"negative_report_pointer": pointer}


def _artifact_pointer_resolves(pointer: str, *, root: Path | None = None) -> bool:
    split = pointer.split(":", 1)
    if len(split) != 2:
        return False
    artifact, local_pointer = split
    payload = _load_artifact_payload(artifact, root=root)
    if not payload:
        return False
    if local_pointer == "$":
        return True
    return pointer_value(payload, local_pointer) is not None


def _coverage_source_with_row_pointers(
    source: Mapping[str, str | None],
    *,
    rows: Sequence[Mapping[str, Any]],
) -> dict[str, str | None]:
    cell = dict(source)
    report_indices = {str(row.get("report")): index for index, row in enumerate(rows) if isinstance(row.get("report"), str)}
    if source.get("component_id") == "gap-head-op" and "gap-head-on-h" in report_indices:
        cell["discovery_level_pointer"] = f"{DISCOVERY_MAP_JSON_ARTIFACT}:$.rows[{report_indices['gap-head-on-h']}].discovery_level"
    return cell


def _coverage_pointer_resolves(pointer: str | None, *, root: Path | None = None) -> bool:
    if pointer is None:
        return False
    if pointer.startswith(f"{DISCOVERY_MAP_JSON_ARTIFACT}:"):
        return True
    return _artifact_pointer_resolves(pointer, root=root)


def _coverage_forbidden_keys(payload: Any, *, path: tuple[str, ...] = ()) -> list[str]:
    found: set[str] = set()
    if isinstance(payload, Mapping):
        for key, value in payload.items():
            key_text = str(key)
            child_path = path + (key_text,)
            if key_text in COVERAGE_FORBIDDEN_KEYS:
                found.add(".".join(child_path))
            found.update(_coverage_forbidden_keys(value, path=child_path))
    elif isinstance(payload, list):
        for index, value in enumerate(payload):
            found.update(_coverage_forbidden_keys(value, path=path + (f"[{index}]",)))
    return sorted(found)


def _coverage_hardgate_rows(cells: Sequence[Mapping[str, Any]], *, root: Path | None = None) -> dict[str, dict[str, str]]:
    copied = _coverage_forbidden_keys({"cells": list(cells)})
    observed = {cell.get("component_id") for cell in cells}
    non_dn_cells = [
        cell
        for cell in cells
        if isinstance(cell.get("component_id"), str) and not str(cell["component_id"]).endswith("-DN")
    ]
    dn_cells = [
        cell
        for cell in cells
        if isinstance(cell.get("component_id"), str) and str(cell["component_id"]).endswith("-DN")
    ]
    gates = {
        "COV-HG1-owner": (
            all(_coverage_pointer_resolves(cell.get("canonical_owner_pointer"), root=root) for cell in cells),
            "every cell has a resolvable canonical owner pointer",
        ),
        "COV-HG2-resolves": (
            all(
                _coverage_pointer_resolves(cell.get(field), root=root)
                for cell in cells
                for field in COVERAGE_POINTER_FIELDS
                if cell.get(field) is not None
            ),
            "every non-null coverage pointer resolves",
        ),
        "COV-HG3-pointer-only": (
            not copied,
            "coverage matrix contains only pointer fields and gate summaries",
        ),
        "COV-HG4-positive-support": (
            all(cell.get("mechanism_certificate_pointer") is not None or cell.get("debt_pointer") is not None for cell in non_dn_cells),
            "positive and model-design cells point to mechanism support or debt",
        ),
        "COV-HG5-dn-witness": (
            all(cell.get("negative_witness_pointer") is not None for cell in dn_cells),
            "DN cells point to canonical negative witnesses",
        ),
        "COV-HG6-complete-set": (
            observed == COVERAGE_COMPONENT_IDS,
            "coverage cells match the required component set",
        ),
    }
    return {
        gate_id: {
            "status": "pass" if passed else "fail",
            "reason": reason if passed else f"{reason}; fail-closed",
        }
        for gate_id, (passed, reason) in gates.items()
    }


def _coverage_cell(
    source: Mapping[str, str | None],
    *,
    hardgates: Mapping[str, Mapping[str, str]],
    root: Path | None = None,
) -> dict[str, str | None]:
    del hardgates
    cell = {field: source.get(field) for field in COVERAGE_CELL_FIELDS if field not in {"hardgate_status", "hardgate_reason"}}
    failed_reasons: list[str] = []
    if not _coverage_pointer_resolves(cell.get("canonical_owner_pointer"), root=root):
        failed_reasons.append("COV-HG1-owner")
    for field in COVERAGE_POINTER_FIELDS:
        pointer = cell.get(field)
        if pointer is not None and not _coverage_pointer_resolves(pointer, root=root):
            failed_reasons.append(f"{field}-unresolved")
    component_id = str(cell.get("component_id", ""))
    if component_id.endswith("-DN"):
        if cell.get("negative_witness_pointer") is None:
            failed_reasons.append("COV-HG5-dn-witness")
    elif cell.get("mechanism_certificate_pointer") is None and cell.get("debt_pointer") is None:
        failed_reasons.append("COV-HG4-positive-support")
    cell["hardgate_status"] = "fail" if failed_reasons else "pass"
    cell["hardgate_reason"] = "pass" if not failed_reasons else "; ".join(sorted(set(failed_reasons)))
    return cell


def _build_coverage_matrix(
    *,
    rows: Sequence[Mapping[str, Any]],
    root: Path | None = None,
) -> dict[str, Any]:
    source_cells = [
        _coverage_source_with_row_pointers(source, rows=rows)
        for source in DISCOVERY_COVERAGE_SOURCES
    ]
    hardgates = _coverage_hardgate_rows(source_cells, root=root)
    cells = [
        _coverage_cell(source, hardgates=hardgates, root=root)
        for source in source_cells
    ]
    hardgates = _coverage_hardgate_rows(cells, root=root)
    cells = [
        _coverage_cell(source, hardgates=hardgates, root=root)
        for source in source_cells
    ]
    return {
        "status": "fail-closed" if any(gate["status"] == "fail" for gate in hardgates.values()) else "pointer-only",
        "hardgates": hardgates,
        "cells": sorted(cells, key=lambda cell: str(cell["component_id"])),
    }


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
        NEGATIVE_DISCOVERY_REPORTS_ARTIFACT,
        NEGATIVE_WITNESSES_ARTIFACT,
        "reports/canonical/negative_witness_mutation_ledger.json",
        "reports/canonical/dgt_mutation_report.json",
        "reports/canonical/new_model_hardgates.json",
        "reports/canonical/discovery-gated-transformer.json",
        MODEL_DESIGN_SUITE_ARTIFACT,
        "reports/canonical/discovery_negative_witness_summary.json",
        "reports/canonical/claim_capsule.json",
        "reports/canonical/claim_graph.json",
        CLAIM_COMPLEXITY_ARTIFACT,
        "reports/canonical/attention_route_derivative_report.json",
        "reports/canonical/transformer_derivative_atlas.json",
        OBSERVED_DEBT_ARTIFACT,
        DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        "reports/canonical/gap_head_transfer_atlas.json",
        "reports/canonical/experiment_proposals.json",
    }
    directory_json = {
        f"reports/canonical/{path.name}"
        for path in sorted((_root(root) / "reports" / "canonical").glob("*.json"))
        if path.name != "index.json" and not path.name.endswith(".fingerprint.json")
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
    source_rows = build_source_discovery_rows(
        root=root,
        canonical_reports=canonical_reports,
        include_sidecars=(_root(root) / NEGATIVE_DISCOVERY_REPORTS_ARTIFACT).exists(),
    )
    negative_indices = _negative_index_by_report(source_rows, root=root)
    rows = [
        _discovery_map_row(row, negative_indices)
        for row in source_rows
        if row.get("discovery_level") != "DN" or str(row.get("report") or "") in negative_indices
    ]
    coverage_matrix = _build_coverage_matrix(rows=rows, root=root)
    return build_discovery_map_payload(
        rows=rows,
        generated_at=timestamp,
        manifest_audit=_manifest_audit(root=root, canonical_reports=canonical_reports),
        coverage_matrix=coverage_matrix,
        root=_root(root),
        expected_coverage_component_ids=COVERAGE_COMPONENT_IDS,
    )


def _dimension_mismatch_discovery_row(
    payload: Mapping[str, Any],
    context: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    context_payloads = {} if context is None else context
    overlay, evidence = _dimension_mismatch_projection(payload, context_payloads)
    projected = dict(payload)
    projected.update(overlay)
    verdict = assign_discovery_level(projected)
    discovery_level = verdict.discovery_level
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
            "anti_triviality_policy",
            "anti_triviality_recommended_level",
            "anti_triviality_failed_gate",
            "anti_triviality_gate_evidence",
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
    if level in {"D5-O", "D5-M"}:
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
        pointer = (
            row.get("negative_report_pointer")
            or row.get("control_pointer")
            or row.get("failed_gate")
            or row.get("debt_row_pointer")
            or row.get("evidence_pointer")
        )
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
    coverage = payload.get("coverage_matrix")
    if isinstance(coverage, Mapping):
        lines.extend(
            [
                "",
                "## Coverage matrix",
                "",
                f"- Status: `{coverage.get('status', '')}`",
                "",
                "| hardgate | status | reason |",
                "| --- | --- | --- |",
            ]
        )
        hardgates = coverage.get("hardgates")
        if isinstance(hardgates, Mapping):
            for gate_id in COVERAGE_HARDGATE_IDS:
                gate = hardgates.get(gate_id)
                if isinstance(gate, Mapping):
                    lines.append(
                        "| "
                        f"`{gate_id}` | "
                        f"`{gate.get('status', '')}` | "
                        f"{gate.get('reason', '')} |"
                    )
        lines.extend(
            [
                "",
                "| group | component | owner pointer | hardgate |",
                "| --- | --- | --- | --- |",
            ]
        )
        cells = coverage.get("cells")
        if isinstance(cells, list):
            sorted_cells = sorted(
                (cell for cell in cells if isinstance(cell, Mapping)),
                key=lambda cell: str(cell.get("component_id", "")),
            )
            for cell in sorted_cells:
                component_id = str(cell.get("component_id", ""))
                group = "negative" if component_id.endswith("-DN") else "positive"
                lines.append(
                    "| "
                    f"`{group}` | "
                    f"`{component_id}` | "
                    f"`{cell.get('canonical_owner_pointer', '')}` | "
                    f"`{cell.get('hardgate_status', '')}` |"
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
