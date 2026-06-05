"""Claim capsule validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence


CLAIM_CAPSULE_SCHEMA_ID = "bedc.quality.claim_capsule"
CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID = "bedc.quality.claim_capsule.run_local"
CLAIM_CAPSULE_JSON_ARTIFACT = "reports/canonical/claim_capsule.json"
CLAIM_CAPSULE_ARTIFACT_ID = "bedc-quality-lab:claim-capsule"


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


def build_claim_capsule_payload(
    *,
    generated_at: str,
    claim_id: str,
    report: str,
    source_artifact: str,
    source_pointer: str,
    claim: Mapping[str, Any] | None,
    not_claimed: Sequence[str] = (),
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
    ClaimCapsule.from_payload(payload)
    return payload
