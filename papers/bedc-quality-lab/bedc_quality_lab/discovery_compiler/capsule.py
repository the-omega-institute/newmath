"""Claim capsule validation."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.construct_validity import CLAIM_CAPSULE_PROJECTION_KEYS
from bedc_quality_lab.discovery_compiler.hardgate_contract import evaluate_u_hardgates
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer, split_artifact_pointer


CLAIM_CAPSULE_SCHEMA_ID = "bedc.quality.claim_capsule"
CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID = "bedc.quality.claim_capsule.run_local"
CLAIM_CAPSULE_JSON_ARTIFACT = "reports/canonical/claim_capsule.json"
CLAIM_CAPSULE_ARTIFACT_ID = "bedc-quality-lab:claim-capsule"
ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE = "bedc.model.architecture_claim_capsule"
TOY_LATENT_PLANNING_CLAIM_CAPSULE_SUBTYPE = "bedc.quality.toy_latent_planning"
ARCHITECTURE_MODEL_CLAIM_REQUIRED_CELLS = (
    "model_id",
    "claim",
    "baselines",
    "forbidden_evidence",
    "required_gates",
    "candidate_pointer",
    "evidence_pointer",
)


def _depends_on_construct_validity(model_claim: Mapping[str, Any]) -> bool:
    gates = model_claim.get("required_gates", ())
    if isinstance(gates, Sequence) and not isinstance(gates, (str, bytes, bytearray)):
        if any(str(gate).startswith("CV-HG") or str(gate) == "construct_validity_hardgates" for gate in gates):
            return True
    return bool(model_claim.get("depends_on_construct_validity"))


def _is_rule_abstraction_claim(model_claim: Mapping[str, Any]) -> bool:
    if model_claim.get("rule_abstraction_claim") is True:
        return True
    text = " ".join(str(model_claim.get(key, "")) for key in ("claim", "claim_type", "allowed_claim"))
    normalized = text.lower().replace("_", "-")
    return "rule-abstraction" in normalized or "rule abstraction" in normalized


def _construct_validity_projection(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    construct_validity = payload.get("construct_validity")
    return construct_validity if isinstance(construct_validity, Mapping) else None


def _require_construct_validity_projection(projection: Mapping[str, Any]) -> None:
    if not set(CLAIM_CAPSULE_PROJECTION_KEYS).issubset(set(projection)):
        raise ValueError("construct_validity projection missing pointer/status cells")
    extra_keys = set(projection).difference(CLAIM_CAPSULE_PROJECTION_KEYS).difference({"base_exceeds_chance"})
    if extra_keys:
        raise ValueError("construct_validity projection has unsupported cells")
    if not isinstance(projection.get("artifact"), str) or not projection["artifact"]:
        raise ValueError("construct_validity projection missing artifact")
    if not isinstance(projection.get("pointer"), str) or not projection["pointer"]:
        raise ValueError("construct_validity projection missing pointer")
    if not isinstance(projection.get("status"), str) or not projection["status"]:
        raise ValueError("construct_validity projection missing status")
    if not isinstance(projection.get("failed_gates"), list):
        raise ValueError("construct_validity projection missing failed_gates")
    if not isinstance(projection.get("owner_pointer"), str) or not projection["owner_pointer"]:
        raise ValueError("construct_validity projection missing owner_pointer")
    base_exceeds_chance = projection.get("base_exceeds_chance")
    if base_exceeds_chance is not None:
        if not isinstance(base_exceeds_chance, Mapping):
            raise ValueError("construct_validity base_exceeds_chance must be an object")
        _require_base_exceeds_chance_cell(base_exceeds_chance)


def _numeric_cell(cell: Mapping[str, Any], key: str) -> float:
    value = cell.get(key)
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        raise ValueError(f"base_exceeds_chance {key} must be numeric")
    return float(value)


def _parent_artifact_pointer(cell: str) -> str | None:
    split = split_artifact_pointer(cell)
    if split is None:
        return None
    artifact, pointer = split
    if not pointer.startswith("$.") or "." not in pointer[2:]:
        return None
    return f"{artifact}:{pointer.rsplit('.', 1)[0]}"


def _require_base_exceeds_chance_resolved_evidence(
    cell: Mapping[str, Any],
    *,
    root: Path,
    evidence_pointer: str,
    base: float,
    chance: float,
    margin: float,
) -> None:
    resolved = resolve_artifact_pointer(root, evidence_pointer)
    if resolved is None:
        raise ValueError("base_exceeds_chance evidence_pointer does not resolve")
    if isinstance(resolved, (int, float)) and not isinstance(resolved, bool):
        if round(float(resolved), 6) != round(base, 6):
            raise ValueError("base_exceeds_chance resolved evidence mismatch")
    parent_pointer = _parent_artifact_pointer(evidence_pointer)
    parent = resolve_artifact_pointer(root, parent_pointer) if parent_pointer is not None else None
    if parent is None:
        return
    if not isinstance(parent, Mapping):
        raise ValueError("base_exceeds_chance resolved evidence parent must be an object")
    owner_control_id = parent.get("base_arm_id", parent.get("fair_control_id"))
    if (
        parent.get("status") != cell.get("status")
        or parent.get("failed_gate") != cell.get("failed_gate")
        or owner_control_id != cell.get("fair_control_id")
        or round(float(parent.get("base_acc_ci95_low", base)), 6) != round(base, 6)
        or round(float(parent.get("chance_accuracy", chance)), 6) != round(chance, 6)
        or round(float(parent.get("margin", margin)), 6) != round(margin, 6)
    ):
        raise ValueError("base_exceeds_chance resolved evidence mismatch")


def _require_base_exceeds_chance_cell(cell: Mapping[str, Any], *, root: Path | None = None) -> None:
    required = {
        "claim",
        "status",
        "fair_control_id",
        "required_fair_control_id",
        "evidence_pointer",
        "base_acc_ci95_low",
        "chance_accuracy",
        "margin",
    }
    missing = [key for key in required if key not in cell]
    if missing:
        raise ValueError(f"base_exceeds_chance missing cells: {', '.join(missing)}")
    claim = cell.get("claim")
    if not isinstance(claim, str) or not claim.strip():
        raise ValueError("base_exceeds_chance claim missing")
    status = cell.get("status")
    if status not in {"pass", "fail"}:
        raise ValueError("base_exceeds_chance status invalid")
    fair_control_id = cell.get("fair_control_id")
    required_fair_control_id = cell.get("required_fair_control_id")
    if not isinstance(fair_control_id, str) or not fair_control_id.strip():
        raise ValueError("base_exceeds_chance fair_control_id missing")
    if fair_control_id != required_fair_control_id:
        raise ValueError("base_exceeds_chance fair_control_id mismatch")
    evidence_pointer = cell.get("evidence_pointer")
    if not isinstance(evidence_pointer, str) or not evidence_pointer.strip():
        raise ValueError("base_exceeds_chance evidence_pointer missing")
    base = _numeric_cell(cell, "base_acc_ci95_low")
    chance = _numeric_cell(cell, "chance_accuracy")
    margin = _numeric_cell(cell, "margin")
    if round(base - chance, 6) != round(margin, 6):
        raise ValueError("base_exceeds_chance margin mismatch")
    if status == "pass" and base <= chance:
        raise ValueError("base_exceeds_chance status contradicts base/chance values")
    if status == "fail" and base > chance:
        raise ValueError("base_exceeds_chance status contradicts base/chance values")
    if status == "fail" and not isinstance(cell.get("failed_gate"), str):
        raise ValueError("base_exceeds_chance failed_gate missing")
    if root is not None:
        _require_base_exceeds_chance_resolved_evidence(
            cell,
            root=root,
            evidence_pointer=evidence_pointer,
            base=base,
            chance=chance,
            margin=margin,
        )


def require_base_exceeds_chance_claim_capsule(
    payload: Mapping[str, Any],
    *,
    root: Path | None = None,
) -> ClaimCapsule:
    capsule = ClaimCapsule.from_payload(payload)
    construct_validity = _construct_validity_projection(capsule.payload)
    if construct_validity is None:
        raise ValueError("claim capsule missing construct_validity.base_exceeds_chance")
    cell = construct_validity.get("base_exceeds_chance")
    if not isinstance(cell, Mapping):
        raise ValueError("claim capsule missing construct_validity.base_exceeds_chance")
    _require_base_exceeds_chance_cell(cell, root=root)
    return capsule


def normalize_claim_capsule_schema_id(payload: Mapping[str, Any]) -> dict[str, Any]:
    schema_id = payload.get("schema_id")
    if schema_id == CLAIM_CAPSULE_SCHEMA_ID:
        return dict(payload)
    if schema_id == CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID:
        return {**dict(payload), "schema_id": CLAIM_CAPSULE_SCHEMA_ID, "run_local_schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID}
    raise ValueError("claim capsule schema_id is invalid")


@dataclass(frozen=True)
class ClaimCapsule:
    claim_id: str
    report: str
    source: str
    source_pointer: str
    status: str
    payload: Mapping[str, Any]

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any]) -> "ClaimCapsule":
        normalized = normalize_claim_capsule_schema_id(payload)
        required = ("claim_id", "report", "source", "source_pointer", "status")
        missing = [key for key in required if not isinstance(normalized.get(key), str) or not str(normalized.get(key)).strip()]
        if missing:
            raise ValueError(f"claim capsule missing required cells: {', '.join(missing)}")
        construct_validity = _construct_validity_projection(normalized)
        if isinstance(construct_validity, Mapping) and "base_exceeds_chance" in construct_validity:
            cell = construct_validity["base_exceeds_chance"]
            if not isinstance(cell, Mapping):
                raise ValueError("construct_validity base_exceeds_chance must be an object")
            _require_base_exceeds_chance_cell(cell)
        return cls(
            claim_id=str(normalized["claim_id"]),
            report=str(normalized["report"]),
            source=str(normalized["source"]),
            source_pointer=str(normalized["source_pointer"]),
            status=str(normalized["status"]),
            payload=normalized,
        )


def require_architecture_claim_capsule(payload: Mapping[str, Any]) -> ClaimCapsule:
    capsule = ClaimCapsule.from_payload(payload)
    normalized = capsule.payload
    if normalized.get("schema_id") != CLAIM_CAPSULE_SCHEMA_ID:
        raise ValueError("architecture claim capsule requires bedc.quality.claim_capsule schema_id")
    if normalized.get("capsule_subtype") != ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE:
        raise ValueError("architecture claim capsule requires capsule_subtype")
    if "capsule_role" in normalized:
        raise ValueError("architecture claim capsule does not accept capsule_role")
    if "architecture_claim_capsule_schema_id" in normalized:
        raise ValueError("architecture claim capsule does not accept architecture_claim_capsule_schema_id")
    model_claim = normalized.get("model_claim")
    if not isinstance(model_claim, Mapping):
        raise ValueError("architecture claim capsule missing model_claim")
    missing = [
        key
        for key in ARCHITECTURE_MODEL_CLAIM_REQUIRED_CELLS
        if key not in model_claim or model_claim.get(key) in (None, "")
    ]
    if missing:
        raise ValueError(f"architecture claim capsule missing model_claim cells: {', '.join(missing)}")
    for key in ("candidate_pointer", "evidence_pointer"):
        pointer_cell = model_claim[key]
        if isinstance(pointer_cell, Mapping):
            if not isinstance(pointer_cell.get("artifact"), str) or not isinstance(pointer_cell.get("pointer"), str):
                raise ValueError(f"architecture claim capsule invalid model_claim pointer cell: {key}")
        elif not isinstance(pointer_cell, str):
            raise ValueError(f"architecture claim capsule invalid model_claim pointer cell: {key}")
    construct_validity = _construct_validity_projection(normalized)
    if _depends_on_construct_validity(model_claim):
        if construct_validity is None:
            raise ValueError("architecture claim capsule requires construct_validity projection")
        _require_construct_validity_projection(construct_validity)
    if construct_validity is not None:
        _require_construct_validity_projection(construct_validity)
        if _is_rule_abstraction_claim(model_claim) and "CV-HG3" in construct_validity["failed_gates"]:
            raise ValueError("architecture claim capsule rejects rule-abstraction claim under CV-HG3 table coverage")
    return capsule


def require_claim_capsule_protocol(
    payload: Mapping[str, Any],
    *,
    root: Path,
    capsule_artifact: str,
    required_not_claimed: Sequence[str],
    cost_pointer: str,
    control_required: bool,
    positive_claim_pointer: str = "$.positive_claim",
    revocation_pointer: str = "$.revocation.rows",
    not_claimed_pointer: str = "$.not_claimed",
) -> dict[str, Any]:
    result = evaluate_u_hardgates(
        payload,
        root=root,
        capsule_artifact=capsule_artifact,
        required_not_claimed=required_not_claimed,
        cost_pointer=cost_pointer,
        control_required=control_required,
        positive_claim_pointer=positive_claim_pointer,
        revocation_pointer=revocation_pointer,
        not_claimed_pointer=not_claimed_pointer,
    )
    if result["status"] != "pass":
        error = ValueError(f"claim capsule protocol failed: {', '.join(result['failed_gates'])}")
        error.protocol_result = result
        raise error
    return result


def build_claim_capsule_payload(
    *,
    generated_at: str,
    claim_id: str,
    report: str,
    source_artifact: str,
    source_pointer: str,
    claim: Mapping[str, Any] | None,
    not_claimed: Sequence[str] = (),
    finite_gate: Mapping[str, Any] | None = None,
    run_local: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    base = {
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "artifact_id": CLAIM_CAPSULE_ARTIFACT_ID,
        "json_artifact": CLAIM_CAPSULE_JSON_ARTIFACT,
        "generated_at": generated_at,
        "producer": "bedc_quality_lab.discovery_compiler.capsule",
        "claim_id": claim_id,
        "report": report,
        "source": source_artifact,
        "source_pointer": source_pointer,
    }
    if claim is None:
        return {**base, "status": "incomplete", "reason": "source claim node is missing"}
    required = (
        "base_level",
        "anti_triviality_status",
        "effective_level",
        "downgrade_reason",
        "terminal_verdict",
        "hypothesis",
        "failed_gate",
        "what_was_learned",
    )
    missing = [key for key in required if key not in claim]
    if missing:
        return {
            **base,
            "status": "incomplete",
            "reason": "source claim node is missing required cells",
            "missing_cells": missing,
        }
    payload = {
        **base,
        "status": "complete",
        "base_level": claim["base_level"],
        "anti_triviality_status": claim["anti_triviality_status"],
        "effective_level": claim["effective_level"],
        "downgrade_reason": claim["downgrade_reason"],
        "terminal_verdict": claim["terminal_verdict"],
        "hypothesis": claim["hypothesis"],
        "failed_gate": claim["failed_gate"],
        "what_was_learned": claim["what_was_learned"],
        "not_claimed": list(not_claimed),
    }
    if finite_gate is not None:
        counts = finite_gate.get("counts")
        pointers = finite_gate.get("pointers")
        gate_not_claimed = finite_gate.get("not_claimed")
        copied_not_claimed = list(gate_not_claimed) if isinstance(gate_not_claimed, Sequence) and not isinstance(gate_not_claimed, (str, bytes, bytearray)) else []
        parity: dict[str, bool] = {}
        if isinstance(counts, Mapping) and isinstance(pointers, Mapping):
            for key in ("positive", "negative", "revocation"):
                pointer_rows = pointers.get(key)
                parity[key] = isinstance(pointer_rows, list) and type(counts.get(key)) is int and len(pointer_rows) == counts[key]
        payload["finite_gate"] = {
            "status": finite_gate.get("status"),
            "counts": dict(counts) if isinstance(counts, Mapping) else {},
            "not_claimed": copied_not_claimed,
            "pointer_count_parity": parity,
        }
    if run_local is not None:
        payload["run_local"] = dict(run_local)
    ClaimCapsule.from_payload(payload)
    return payload


def build_architecture_claim_capsule_payload(
    *,
    generated_at: str,
    claim_id: str,
    report: str,
    source_artifact: str,
    source_pointer: str,
    model_claim: Mapping[str, Any],
    not_claimed: Sequence[str] = (),
    construct_validity: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    payload = {
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
        "artifact_id": CLAIM_CAPSULE_ARTIFACT_ID,
        "json_artifact": CLAIM_CAPSULE_JSON_ARTIFACT,
        "generated_at": generated_at,
        "producer": "bedc_quality_lab.discovery_compiler.capsule",
        "claim_id": claim_id,
        "report": report,
        "source": source_artifact,
        "source_pointer": source_pointer,
        "status": "complete",
        "model_claim": dict(model_claim),
        "not_claimed": list(not_claimed),
    }
    if construct_validity is not None:
        payload["construct_validity"] = dict(construct_validity)
    require_architecture_claim_capsule(payload)
    return payload
