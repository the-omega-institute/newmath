"""Claim capsule validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from bedc_quality_lab.construct_validity import CLAIM_CAPSULE_PROJECTION_KEYS


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
    if set(projection) != set(CLAIM_CAPSULE_PROJECTION_KEYS):
        raise ValueError("construct_validity projection must contain only pointer/status cells")
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
