"""Claim capsule validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence


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
    require_architecture_claim_capsule(payload)
    return payload
