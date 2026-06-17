"""Model-comparison row semantics and evidence-chain hardgates."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.evidence_provenance import evidence_provenance_pointer_for_report

JSON_ARTIFACT = "reports/canonical/model-comparison.json"
DGT_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
SEMANTIC_POINTER = f"{JSON_ARTIFACT}:$.comparisons[*].semantic"
DGT_CONTROL_SEMANTIC_POINTER = f"{JSON_ARTIFACT}:$.comparisons[0].semantic"
D5_M_SCOPE_POINTER = f"{DGT_ARTIFACT}:$.d5_m_scope"
OWNER_REPORT = "model-comparison"
OWNER_POINTER = evidence_provenance_pointer_for_report(OWNER_REPORT)
COMPARISON_TYPES = frozenset({"trained_vs_trained", "deterministic_projection", "spec"})
TRAINING_STATUSES = frozenset({"trained", "not_trained", "not_applicable"})
METRIC_PROVENANCE_VALUES = frozenset(
    {
        "measured_training",
        "deterministic_projection",
        "protocol_field",
        "declared_constant",
        "arm_branch",
    }
)
MC_SEMANTIC_HARDGATE_IDS = tuple(f"MC-HG{index}" for index in range(11, 15))


@dataclass(frozen=True)
class SemanticOwner:
    evidence_type: str
    metric_provenance: str
    metric_owner_pointer: str | None
    discovery_owner_pointer: str


def _model_by_id(models: Sequence[Mapping[str, Any]], model_id: str) -> Mapping[str, Any] | None:
    matches = [row for row in models if row.get("model_id") == model_id]
    return matches[0] if len(matches) == 1 else None


def _first_metric_row(owner_section: Mapping[str, Any] | None, report: str) -> Mapping[str, Any] | None:
    rows = owner_section.get("metric_rows") if isinstance(owner_section, Mapping) else None
    if not isinstance(rows, list):
        return None
    matches = [row for row in rows if isinstance(row, Mapping) and row.get("report") == report]
    return matches[0] if len(matches) == 1 else None


def _discovery_owner_row(owner_section: Mapping[str, Any] | None, report: str) -> Mapping[str, Any] | None:
    rows = owner_section.get("discovery_rows_by_report") if isinstance(owner_section, Mapping) else None
    row = rows.get(report) if isinstance(rows, Mapping) else None
    return row if isinstance(row, Mapping) else None


def _semantic_owner(owner_section: Mapping[str, Any] | None) -> SemanticOwner:
    discovery = _discovery_owner_row(owner_section, OWNER_REPORT)
    metric = _first_metric_row(owner_section, OWNER_REPORT)
    evidence_type = str(discovery.get("evidence_type")) if isinstance(discovery, Mapping) and isinstance(discovery.get("evidence_type"), str) else "deterministic_projection"
    metric_provenance = str(metric.get("source_type")) if isinstance(metric, Mapping) and isinstance(metric.get("source_type"), str) else "deterministic_projection"
    metric_pointer = None
    if isinstance(metric, Mapping):
        pointers = discovery.get("metric_provenance_pointers") if isinstance(discovery, Mapping) else None
        if isinstance(pointers, list) and pointers and isinstance(pointers[0], str):
            metric_pointer = pointers[0]
    return SemanticOwner(
        evidence_type=evidence_type,
        metric_provenance=metric_provenance,
        metric_owner_pointer=metric_pointer,
        discovery_owner_pointer=OWNER_POINTER,
    )


def _comparison_semantic(
    *,
    owner: SemanticOwner,
    construct_validity_pointer: str | None = None,
) -> dict[str, Any]:
    return {
        "comparison_type": "deterministic_projection",
        "evidence_type_pointer": owner.discovery_owner_pointer,
        "evidence_type": owner.evidence_type,
        "metric_provenance_pointer": owner.metric_owner_pointer,
        "construct_validity_pointer": construct_validity_pointer,
        "training_status": "not_trained",
        "metric_provenance": owner.metric_provenance,
        "fair_input_access": False,
        "ood_solvability": None,
        "baseline_validity": True,
        "allowed_evidence_chain": False,
        "boundary_reason": "deterministic projection cannot support trained-model empirical superiority",
    }


def build_comparisons(
    models: Sequence[Mapping[str, Any]],
    *,
    evidence_owner_section: Mapping[str, Any] | None = None,
) -> list[dict[str, Any]]:
    owner = _semantic_owner(evidence_owner_section)
    dgt = _model_by_id(models, "dgt")
    base = _model_by_id(models, "base_transformer")
    matched = _model_by_id(models, "matched_random_structural_control")
    comparisons: list[dict[str, Any]] = []
    if dgt is not None and base is not None and matched is not None:
        comparisons.append(
            {
                "comparison_id": "dgt_control_projection",
                "candidate_model_id": "dgt",
                "baseline_model_ids": ["base_transformer", "matched_random_structural_control"],
                "model_pointers": {
                    "candidate": f"{JSON_ARTIFACT}:$.models[0]",
                    "baselines": [f"{JSON_ARTIFACT}:$.models[1]", f"{JSON_ARTIFACT}:$.models[2]"],
                },
                "semantic": _comparison_semantic(owner=owner),
            }
        )
    return comparisons


def _semantic_errors(
    semantic: Mapping[str, Any],
    *,
    root: Path | None = None,
    pointer_path: str,
) -> list[str]:
    errors: list[str] = []
    comparison_type = semantic.get("comparison_type")
    training_status = semantic.get("training_status")
    metric_provenance = semantic.get("metric_provenance")
    allowed = semantic.get("allowed_evidence_chain")
    evidence_type_pointer = semantic.get("evidence_type_pointer")
    evidence_type = semantic.get("evidence_type")
    if comparison_type not in COMPARISON_TYPES:
        errors.append(f"{pointer_path}.comparison_type unsupported")
    if training_status not in TRAINING_STATUSES:
        errors.append(f"{pointer_path}.training_status unsupported")
    if metric_provenance not in METRIC_PROVENANCE_VALUES:
        errors.append(f"{pointer_path}.metric_provenance unsupported")
    if not isinstance(evidence_type_pointer, str) or not evidence_type_pointer:
        errors.append(f"{pointer_path}.evidence_type_pointer missing")
    elif root is not None and resolve_artifact_pointer(root, evidence_type_pointer) is None:
        errors.append(f"{pointer_path}.evidence_type_pointer unresolved")
    if semantic.get("metric_provenance_pointer") is not None:
        metric_pointer = semantic.get("metric_provenance_pointer")
        if not isinstance(metric_pointer, str) or (root is not None and resolve_artifact_pointer(root, metric_pointer) is None):
            errors.append(f"{pointer_path}.metric_provenance_pointer unresolved")
    construct_pointer = semantic.get("construct_validity_pointer")
    if construct_pointer is not None and (not isinstance(construct_pointer, str) or root is not None and resolve_artifact_pointer(root, construct_pointer) is None):
        errors.append(f"{pointer_path}.construct_validity_pointer unresolved")
    if comparison_type in {"deterministic_projection", "spec"}:
        if training_status == "trained":
            errors.append(f"{pointer_path}.training_status must not be trained")
        if metric_provenance == "measured_training":
            errors.append(f"{pointer_path}.metric_provenance must not be measured_training")
        if allowed is not False:
            errors.append(f"{pointer_path}.allowed_evidence_chain must be false")
        if evidence_type == "empirical_training_clean":
            errors.append(f"{pointer_path}.evidence_type must not be empirical_training_clean")
    if comparison_type == "trained_vs_trained":
        if training_status != "trained":
            errors.append(f"{pointer_path}.training_status must be trained")
        if metric_provenance != "measured_training":
            errors.append(f"{pointer_path}.metric_provenance must be measured_training")
        if semantic.get("fair_input_access") is not True:
            errors.append(f"{pointer_path}.fair_input_access must be true")
        if semantic.get("baseline_validity") is not True:
            errors.append(f"{pointer_path}.baseline_validity must be true")
        if evidence_type != "empirical_training_clean":
            errors.append(f"{pointer_path}.evidence_type must be empirical_training_clean")
    if not isinstance(semantic.get("boundary_reason"), str) or not semantic.get("boundary_reason"):
        errors.append(f"{pointer_path}.boundary_reason missing")
    return errors


def validate_model_comparison_payload(payload: Mapping[str, Any], *, root: Path | None = None) -> list[str]:
    errors: list[str] = []
    comparisons = payload.get("comparisons")
    if not isinstance(comparisons, list) or not comparisons:
        return ["model-comparison comparisons missing"]
    ids: list[str] = []
    for index, row in enumerate(comparisons):
        if not isinstance(row, Mapping):
            errors.append(f"$.comparisons[{index}] must be an object")
            continue
        comparison_id = row.get("comparison_id")
        if not isinstance(comparison_id, str) or not comparison_id:
            errors.append(f"$.comparisons[{index}].comparison_id missing")
        else:
            ids.append(comparison_id)
        semantic = row.get("semantic")
        if not isinstance(semantic, Mapping):
            errors.append(f"$.comparisons[{index}].semantic missing")
            continue
        errors.extend(_semantic_errors(semantic, root=root, pointer_path=f"$.comparisons[{index}].semantic"))
    if len(ids) != len(set(ids)):
        errors.append("model-comparison comparison_id values must be unique")
    return errors


def semantic_hardgates(payload: Mapping[str, Any], *, root: Path | None = None) -> dict[str, dict[str, Any]]:
    errors = validate_model_comparison_payload(payload, root=root)
    comparisons = payload.get("comparisons")
    semantic_rows = [row.get("semantic") for row in comparisons] if isinstance(comparisons, list) else []
    all_semantic = bool(semantic_rows) and all(isinstance(row, Mapping) for row in semantic_rows)
    owner_pointers = [
        row.get("evidence_type_pointer")
        for row in semantic_rows
        if isinstance(row, Mapping)
    ]
    semantic_valid = not errors
    projection_rows_closed = all(
        row.get("comparison_type") not in {"deterministic_projection", "spec"}
        or (
            row.get("metric_provenance") != "measured_training"
            and row.get("training_status") != "trained"
            and row.get("allowed_evidence_chain") is False
        )
        for row in semantic_rows
        if isinstance(row, Mapping)
    )
    boundaries = all(
        isinstance(row, Mapping)
        and isinstance(row.get("boundary_reason"), str)
        and "trained-model empirical superiority" in row.get("boundary_reason", "")
        for row in semantic_rows
    )
    gate_values = {
        "MC-HG11": (
            all_semantic and semantic_valid,
            "comparison rows carry exactly one validated semantic object",
        ),
        "MC-HG12": (
            bool(owner_pointers) and all(pointer == OWNER_POINTER for pointer in owner_pointers) and semantic_valid,
            "comparison semantics point to the evidence provenance owner row",
        ),
        "MC-HG13": (
            projection_rows_closed and semantic_valid,
            "deterministic projection rows cannot enter measured-training evidence chains",
        ),
        "MC-HG14": (
            boundaries and semantic_valid,
            "projection rows carry trained-model claim boundaries",
        ),
    }
    return {
        gate_id: {
            "gate_id": gate_id,
            "status": "pass" if passed else "fail",
            "reason": reason if passed else f"{reason}; fail-closed",
        }
        for gate_id, (passed, reason) in gate_values.items()
    }
