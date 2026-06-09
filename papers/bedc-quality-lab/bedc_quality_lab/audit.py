"""Self-cited certificate evidence audit."""

from __future__ import annotations

from typing import Any, Mapping

from bedc_quality_lab.claim_projection import project_certificate_guided_claim
from bedc_quality_lab.schema import SCHEMA_ID


AUDIT_CONSISTENT = "consistent"
AUDIT_DIVERGENT = "divergent"
AUDIT_UNVERIFIABLE = "unverifiable"
_REQUIRED_PROJECTION_FIELDS = (
    "main_claim_status",
    "claim_gate",
    "main_verdict",
    "matched_random_baseline",
    "evidence_basis",
)


def _recorded_status(certificate_payload: Mapping[str, Any] | None) -> str | None:
    if certificate_payload is None:
        return None
    for key in ("main_claim_status", "claim_status", "status"):
        value = certificate_payload.get(key)
        if isinstance(value, str) and value:
            return value
    return None


def _row(
    *,
    timestamp_iso: str,
    audit_status: str,
    recorded_status: str | None,
    recomputed_status: str | None,
    reason: str,
    evidence_basis: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "event": "certified-claim-audit",
        "timestamp": timestamp_iso,
        "audit_status": audit_status,
        "recorded_status": recorded_status,
        "recomputed_status": recomputed_status,
        "reason": reason,
        "evidence_basis": dict(evidence_basis),
    }


def _decision(
    *,
    timestamp_iso: str,
    audit_status: str,
    recorded_status: str | None,
    recomputed_status: str | None,
    reason: str,
    evidence_basis: Mapping[str, Any],
) -> dict[str, Any]:
    row = _row(
        timestamp_iso=timestamp_iso,
        audit_status=audit_status,
        recorded_status=recorded_status,
        recomputed_status=recomputed_status,
        reason=reason,
        evidence_basis=evidence_basis,
    )
    return {
        "audit_status": audit_status,
        "recorded_status": recorded_status,
        "recomputed_status": recomputed_status,
        "reason": reason,
        "evidence_basis": dict(evidence_basis),
        "audit_row": row,
    }


def _unverifiable(
    *,
    timestamp_iso: str,
    recorded_status: str | None,
    reason: str,
    evidence_basis: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return _decision(
        timestamp_iso=timestamp_iso,
        audit_status=AUDIT_UNVERIFIABLE,
        recorded_status=recorded_status,
        recomputed_status=None,
        reason=reason,
        evidence_basis=evidence_basis or {},
    )


def _schema_status(evidence_payload: Mapping[str, Any]) -> str | None:
    schema_id = evidence_payload.get("schema_id")
    if schema_id is None:
        return "missing-schema-id"
    if schema_id != SCHEMA_ID:
        return "schema-id-mismatch"
    return None


def audit_certified_claim(
    certificate_payload: Mapping[str, Any] | None,
    evidence_payload: Mapping[str, Any],
    *,
    timestamp_iso: str,
) -> dict[str, Any]:
    recorded_status = _recorded_status(certificate_payload)
    schema_reason = _schema_status(evidence_payload)
    if schema_reason is not None:
        return _unverifiable(
            timestamp_iso=timestamp_iso,
            recorded_status=recorded_status,
            reason=schema_reason,
            evidence_basis={"source_schema_id": evidence_payload.get("schema_id")},
        )

    try:
        projection = project_certificate_guided_claim(evidence_payload)
    except (KeyError, TypeError, ValueError) as exc:
        return _unverifiable(
            timestamp_iso=timestamp_iso,
            recorded_status=recorded_status,
            reason=f"projection-unavailable:{exc}",
        )

    projection_payload = projection.to_dict()
    missing = [field for field in _REQUIRED_PROJECTION_FIELDS if field not in projection_payload]
    if missing:
        return _unverifiable(
            timestamp_iso=timestamp_iso,
            recorded_status=recorded_status,
            reason=f"projection-fields-missing:{','.join(missing)}",
            evidence_basis=projection_payload.get("evidence_basis", {}),
        )

    recomputed_status = projection.main_claim_status
    evidence_basis = projection.evidence_basis
    if recorded_status is None:
        return _unverifiable(
            timestamp_iso=timestamp_iso,
            recorded_status=recorded_status,
            reason="recorded-status-missing",
            evidence_basis=evidence_basis,
        )

    if recorded_status == recomputed_status:
        return _decision(
            timestamp_iso=timestamp_iso,
            audit_status=AUDIT_CONSISTENT,
            recorded_status=recorded_status,
            recomputed_status=recomputed_status,
            reason="recorded-status-matches-recomputed-status",
            evidence_basis=evidence_basis,
        )

    return _decision(
        timestamp_iso=timestamp_iso,
        audit_status=AUDIT_DIVERGENT,
        recorded_status=recorded_status,
        recomputed_status=recomputed_status,
        reason="recorded-status-differs-from-recomputed-status",
        evidence_basis=evidence_basis,
    )
