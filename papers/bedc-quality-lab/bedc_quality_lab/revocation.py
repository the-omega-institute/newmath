"""Lab-local certified claim revocation transition."""

from __future__ import annotations

from typing import Any, Mapping


EMPTY_LEDGER_ROW: dict[str, Any] = {}
POSITIVE_STATUS = "positive"
TRADEOFF_STATUS = "audit-improvement-tradeoff"
FAIL_CLOSED_STATUS = "mixed"


def _status(payload: Mapping[str, Any]) -> str:
    for key in ("main_claim_status", "claim_status", "status"):
        value = payload.get(key)
        if isinstance(value, str) and value:
            return value
    return "unknown"


def _fresh_gate(fresh_projection: Mapping[str, Any]) -> Mapping[str, Any] | None:
    gate = fresh_projection.get("claim_gate")
    return gate if isinstance(gate, Mapping) else None


def _fresh_ci_low(gate: Mapping[str, Any]) -> float | None:
    for key in ("training_quality_q_ci95_low", "quality_q_ci95_low"):
        value = gate.get(key)
        if isinstance(value, (int, float)):
            return float(value)
    return None


def _fresh_ci_status(gate: Mapping[str, Any]) -> str | None:
    for key in ("training_paired_ci_status", "paired_ci_status"):
        value = gate.get(key)
        if isinstance(value, str) and value:
            return value
    return None


def _fresh_tradeoff(gate: Mapping[str, Any]) -> bool | None:
    for key in ("training_audit_improvement_tradeoff", "audit_improvement_tradeoff"):
        value = gate.get(key)
        if isinstance(value, bool):
            return value
    return None


def _evidence_delta(
    *,
    old_status: str,
    fresh_status: str,
    ci_low: float | None,
    ci_status: str | None,
    blockers: Any,
    tradeoff: bool | None,
) -> dict[str, Any]:
    return {
        "old_status": old_status,
        "fresh_status": fresh_status,
        "quality_q_ci95_low": ci_low,
        "paired_ci_status": ci_status,
        "audit_improvement_tradeoff": tradeoff,
        "blockers": list(blockers) if isinstance(blockers, list) else [],
    }


def _ledger_row(
    *,
    timestamp_iso: str,
    old_status: str,
    new_status: str,
    reason: str,
    evidence_delta: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "event": "certified-claim-revocation",
        "timestamp": timestamp_iso,
        "old_status": old_status,
        "new_status": new_status,
        "reason": reason,
        "evidence_delta": dict(evidence_delta),
    }


def _decision(
    *,
    downgraded: bool,
    old_status: str | None,
    new_status: str | None,
    reason: str,
    evidence_delta: Mapping[str, Any],
    ledger_row: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "downgraded": bool(downgraded),
        "old_status": old_status,
        "new_status": new_status,
        "reason": reason,
        "evidence_delta": dict(evidence_delta),
        "ledger_row": dict(ledger_row) if ledger_row is not None else EMPTY_LEDGER_ROW,
    }


def reevaluate_certified_claim(
    certificate_payload: Mapping[str, Any] | None,
    fresh_projection: Mapping[str, Any],
    *,
    timestamp_iso: str,
) -> dict[str, Any]:
    if certificate_payload is None:
        return _decision(
            downgraded=False,
            old_status=None,
            new_status=None,
            reason="no-certified-claim",
            evidence_delta={},
        )

    old_status = _status(certificate_payload)
    if old_status != POSITIVE_STATUS:
        return _decision(
            downgraded=False,
            old_status=old_status,
            new_status=old_status,
            reason="old-certificate-not-positive",
            evidence_delta={"old_status": old_status},
        )

    fresh_status = _status(fresh_projection)
    gate = _fresh_gate(fresh_projection)
    if gate is None:
        evidence_delta = _evidence_delta(
            old_status=old_status,
            fresh_status=fresh_status,
            ci_low=None,
            ci_status=None,
            blockers=[],
            tradeoff=None,
        )
        row = _ledger_row(
            timestamp_iso=timestamp_iso,
            old_status=old_status,
            new_status=FAIL_CLOSED_STATUS,
            reason="malformed-fresh-claim-gate",
            evidence_delta=evidence_delta,
        )
        return _decision(
            downgraded=True,
            old_status=old_status,
            new_status=FAIL_CLOSED_STATUS,
            reason="malformed-fresh-claim-gate",
            evidence_delta=evidence_delta,
            ledger_row=row,
        )

    ci_low = _fresh_ci_low(gate)
    ci_status = _fresh_ci_status(gate)
    tradeoff = _fresh_tradeoff(gate)
    blockers = gate.get("blockers")
    evidence_delta = _evidence_delta(
        old_status=old_status,
        fresh_status=fresh_status,
        ci_low=ci_low,
        ci_status=ci_status,
        blockers=blockers,
        tradeoff=tradeoff,
    )

    if tradeoff is True:
        reason = "audit-improvement-tradeoff"
        row = _ledger_row(
            timestamp_iso=timestamp_iso,
            old_status=old_status,
            new_status=TRADEOFF_STATUS,
            reason=reason,
            evidence_delta=evidence_delta,
        )
        return _decision(
            downgraded=True,
            old_status=old_status,
            new_status=TRADEOFF_STATUS,
            reason=reason,
            evidence_delta=evidence_delta,
            ledger_row=row,
        )

    if ci_low is None or ci_status is None:
        reason = "malformed-fresh-claim-gate"
        row = _ledger_row(
            timestamp_iso=timestamp_iso,
            old_status=old_status,
            new_status=FAIL_CLOSED_STATUS,
            reason=reason,
            evidence_delta=evidence_delta,
        )
        return _decision(
            downgraded=True,
            old_status=old_status,
            new_status=FAIL_CLOSED_STATUS,
            reason=reason,
            evidence_delta=evidence_delta,
            ledger_row=row,
        )

    if ci_status != "ok" or ci_low <= 0.0:
        reason = "paired-quality-ci-weakened"
        new_status = fresh_status if fresh_status != POSITIVE_STATUS else FAIL_CLOSED_STATUS
        row = _ledger_row(
            timestamp_iso=timestamp_iso,
            old_status=old_status,
            new_status=new_status,
            reason=reason,
            evidence_delta=evidence_delta,
        )
        return _decision(
            downgraded=True,
            old_status=old_status,
            new_status=new_status,
            reason=reason,
            evidence_delta=evidence_delta,
            ledger_row=row,
        )

    if fresh_status != POSITIVE_STATUS:
        reason = "fresh-claim-gate-not-positive"
        row = _ledger_row(
            timestamp_iso=timestamp_iso,
            old_status=old_status,
            new_status=fresh_status,
            reason=reason,
            evidence_delta=evidence_delta,
        )
        return _decision(
            downgraded=True,
            old_status=old_status,
            new_status=fresh_status,
            reason=reason,
            evidence_delta=evidence_delta,
            ledger_row=row,
        )

    return _decision(
        downgraded=False,
        old_status=old_status,
        new_status=fresh_status,
        reason="fresh-claim-remains-positive",
        evidence_delta=evidence_delta,
    )
