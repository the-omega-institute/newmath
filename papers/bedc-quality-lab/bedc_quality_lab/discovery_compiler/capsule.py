"""Claim capsule validation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence


CLAIM_CAPSULE_SCHEMA_ID = "bedc.quality.claim_capsule"
CLAIM_CAPSULE_JSON_ARTIFACT = "reports/canonical/claim_capsule.json"
CLAIM_CAPSULE_ARTIFACT_ID = "bedc-quality-lab:claim-capsule"


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
        required = ("claim_id", "report", "source", "source_pointer", "status")
        missing = [key for key in required if not isinstance(payload.get(key), str) or not str(payload.get(key)).strip()]
        if missing:
            raise ValueError(f"claim capsule missing required cells: {', '.join(missing)}")
        if payload.get("schema_id") != CLAIM_CAPSULE_SCHEMA_ID:
            raise ValueError("claim capsule schema_id is invalid")
        return cls(
            claim_id=str(payload["claim_id"]),
            report=str(payload["report"]),
            source=str(payload["source"]),
            source_pointer=str(payload["source_pointer"]),
            status=str(payload["status"]),
            payload=payload,
        )


def build_claim_capsule_payload(
    *,
    generated_at: str,
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
        "claim_id": "claim:dimension-mismatch-debt-transfer",
        "report": "dimension-mismatch-debt-transfer",
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
