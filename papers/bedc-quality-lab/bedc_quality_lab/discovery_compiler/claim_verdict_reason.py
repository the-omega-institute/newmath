"""Claim verdict reason taxonomy and fail-closed checks."""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any, Mapping


DISCOVERY_LEVEL_D4_POSITIVE = "discovery-level-D4-positive"
D5O_OPERATIONAL = "D5O-operational"
D5M_TRAINING_MECHANISM = "D5M-training-mechanism"
PROJECTED_DISCOVERY_REQUIRED = "projected-discovery-required"
MECHANISM_NOT_CLOSED = "mechanism-not-closed"
NEGATIVE_DISCOVERY_FAILED_GATE_PREFIX = "negative-discovery-failed-gate"
SOURCE_INSUFFICIENT = "source-insufficient"
MODEL_COMPARISON_NOT_READY = "model-comparison-not-ready"
POSITIVE_DISCOVERY_GATES_PASS = "positive-discovery-gates-pass"

FIXED_TAXONOMY = frozenset(
    {
        DISCOVERY_LEVEL_D4_POSITIVE,
        D5O_OPERATIONAL,
        D5M_TRAINING_MECHANISM,
        PROJECTED_DISCOVERY_REQUIRED,
        MECHANISM_NOT_CLOSED,
        SOURCE_INSUFFICIENT,
        MODEL_COMPARISON_NOT_READY,
        POSITIVE_DISCOVERY_GATES_PASS,
    }
)


@dataclass(frozen=True)
class ClaimVerdictReasonBasis:
    claim_verdict: str
    discovery_level: str | None = None
    failed_gate: str | None = None
    scorecard_ready: bool | None = None
    report: str | None = None
    mechanism_open: bool = False
    source_insufficient: bool = False
    model_comparison_ready: bool | None = None
    claim_verdict_pointer: str | None = None


def failed_gate_reason_token(value: Any) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError("negative discovery reason requires failed_gate")
    token = value
    if token == "$":
        return "root"
    if token.startswith("$."):
        token = token[2:]
    token = token.replace("[", ".").replace("]", "")
    token = re.sub(r"[^A-Za-z0-9]+", "-", token).strip("-").lower()
    if not token:
        raise ValueError("negative discovery reason requires failed_gate token")
    return token


def negative_failed_gate_reason(value: Any) -> str:
    return f"{NEGATIVE_DISCOVERY_FAILED_GATE_PREFIX}:{failed_gate_reason_token(value)}"


def reason_for_claim_verdict(basis: ClaimVerdictReasonBasis) -> str:
    if basis.claim_verdict == "negative_discovery":
        return negative_failed_gate_reason(basis.failed_gate)
    if basis.source_insufficient:
        return SOURCE_INSUFFICIENT
    if basis.claim_verdict == "mechanism_not_closed" or basis.mechanism_open:
        return MECHANISM_NOT_CLOSED
    if basis.report == "discovery-gated-transformer" and basis.discovery_level == "D0" and basis.model_comparison_ready is False:
        return MODEL_COMPARISON_NOT_READY
    if basis.report == "discovery-gated-transformer" and basis.claim_verdict == "accepted_positive_discovery":
        return POSITIVE_DISCOVERY_GATES_PASS
    if basis.discovery_level == "D5-M":
        return D5M_TRAINING_MECHANISM
    if basis.discovery_level == "D5-O":
        return D5O_OPERATIONAL
    if basis.discovery_level == "D4" and basis.claim_verdict == "accepted_positive_discovery":
        return DISCOVERY_LEVEL_D4_POSITIVE
    if basis.claim_verdict in {
        "projected_discovery_required",
        "projected_positive_discovery",
        "raw_operational_evidence_pass",
    }:
        return PROJECTED_DISCOVERY_REQUIRED
    raise ValueError(f"unsupported claim verdict reason basis: {basis}")


def validate_claim_verdict_reason(row: Mapping[str, Any], *, basis: ClaimVerdictReasonBasis | None = None) -> None:
    reason = row.get("reason")
    if not isinstance(reason, str) or not reason:
        raise ValueError("claim verdict reason must be non-empty")
    if reason == NEGATIVE_DISCOVERY_FAILED_GATE_PREFIX:
        raise ValueError("bare negative discovery failed-gate reason is not allowed")
    if reason == "discovery-level-DN":
        raise ValueError("bare DN reason is not allowed")
    if reason.startswith(f"{NEGATIVE_DISCOVERY_FAILED_GATE_PREFIX}:"):
        suffix = reason.removeprefix(f"{NEGATIVE_DISCOVERY_FAILED_GATE_PREFIX}:")
        if not suffix:
            raise ValueError("negative discovery reason requires failed_gate token")
    if basis is not None:
        expected = reason_for_claim_verdict(basis)
        if reason != expected:
            raise ValueError(f"claim verdict reason mismatch: expected {expected}, got {reason}")
        if basis.scorecard_ready is True and reason in {SOURCE_INSUFFICIENT, MODEL_COMPARISON_NOT_READY}:
            raise ValueError("scorecard-ready claim verdict cannot use not-ready reason")
    elif _looks_like_owned_taxonomy(reason) and reason not in FIXED_TAXONOMY and not reason.startswith(
        f"{NEGATIVE_DISCOVERY_FAILED_GATE_PREFIX}:"
    ):
        raise ValueError(f"unsupported claim verdict reason taxonomy: {reason}")


def _looks_like_owned_taxonomy(reason: str) -> bool:
    return (
        reason.startswith("discovery-level-D")
        or reason.startswith("D5")
        or reason
        in {
            PROJECTED_DISCOVERY_REQUIRED,
            MECHANISM_NOT_CLOSED,
            SOURCE_INSUFFICIENT,
            MODEL_COMPARISON_NOT_READY,
            POSITIVE_DISCOVERY_GATES_PASS,
        }
        or reason.startswith("negative-discovery")
        or reason.startswith("positive-discovery")
    )


def reason_basis_from_negative_owner(
    owner_row: Mapping[str, Any],
    *,
    claim_verdict_pointer: str | None = None,
) -> ClaimVerdictReasonBasis:
    return ClaimVerdictReasonBasis(
        claim_verdict="negative_discovery",
        discovery_level=str(owner_row.get("discovery_level") or "DN"),
        failed_gate=owner_row.get("failed_gate") if isinstance(owner_row.get("failed_gate"), str) else None,
        report=owner_row.get("report") if isinstance(owner_row.get("report"), str) else None,
        claim_verdict_pointer=claim_verdict_pointer,
    )
