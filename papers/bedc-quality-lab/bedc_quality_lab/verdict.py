"""Terminal certified claim verdict synthesis."""

from __future__ import annotations

from typing import Any, Mapping

from bedc_quality_lab.audit import AUDIT_CONSISTENT, audit_certified_claim
from bedc_quality_lab.claim_projection import project_certificate_guided_claim
from bedc_quality_lab.rejection import MALFORMED_EVIDENCE, reject_certified_claim
from bedc_quality_lab.revocation import reevaluate_certified_claim


ACCEPTED = "accepted"
REJECTED = "rejected"
DEMOTED = "demoted"
LEDGER_ONLY = "ledger-only"
POSITIVE_DISCOVERY = "positive-discovery"
POSITIVE_STATUS = "positive"
SCORECARD_PATH = "$.quality_scorecard.rows"
QUALITY_SCORECARD_METRICS = (
    "CertCov",
    "DebtQ",
    "CriticalDebt",
    "LedgerCompleteness",
    "ClassifierShiftCount",
    "PositiveDiscoveryCount",
    "AuditImprovementCount",
    "NegativeResultCount",
    "ScopeCompleteness",
    "CostProtocolCompleteness",
    "HardeningCoverage",
    "OverclaimRate",
)

_FLAT_BASIS_KEYS = (
    "reason",
    "malformed_detail",
    "source_schema_id",
    "source_artifact",
    "record_roles",
    "main_pair",
    "baseline_pair",
    "paired_quality_q_ci",
    "training_claim_gate_keys",
    "main_claim_status",
    "claim_gate",
    "main_verdict",
    "main_surface_delta_count",
    "main_shift_information",
    "main_structural_discovery",
    "control_verdict",
    "control_surface_delta_count",
    "control_shift_information",
    "control_structural_discovery",
    "control_positive_discovery",
    "forbidden_claim_term_hits",
    "rejected",
    "rejection_reason",
    "audit_status",
    "recorded_status",
    "recomputed_status",
    "audit_reason",
    "downgraded",
    "old_status",
    "new_status",
    "revocation_reason",
    "quality_q_ci95_low",
    "paired_ci_status",
    "audit_improvement_tradeoff",
    "failed_gate",
    "hardgate_status",
    "blockers",
    "ledger_row_event",
    "scorecard_ready",
    "net_positive_signal",
)


def _empty_basis() -> dict[str, Any]:
    basis = {key: None for key in _FLAT_BASIS_KEYS}
    basis["record_roles"] = []
    basis["main_pair"] = []
    basis["baseline_pair"] = []
    basis["training_claim_gate_keys"] = []
    basis["forbidden_claim_term_hits"] = []
    basis["blockers"] = []
    basis["scorecard_ready"] = False
    basis["net_positive_signal"] = False
    return basis


def _decision(
    *,
    verdict: str,
    reason: str,
    evidence_basis: Mapping[str, Any],
    timestamp_iso: str,
) -> dict[str, Any]:
    basis = _empty_basis()
    for key, value in evidence_basis.items():
        if key in basis:
            basis[key] = value
    basis["reason"] = reason
    return {
        "verdict": verdict,
        "reason": reason,
        "evidence_basis": basis,
        "decided_at": timestamp_iso,
    }


def _scorecard_payload(evidence_payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    for key in ("quality_scorecard", "scorecard"):
        value = evidence_payload.get(key)
        if isinstance(value, Mapping):
            return value
    return None


def _scorecard_readiness(evidence_payload: Mapping[str, Any]) -> tuple[bool | None, str | None]:
    scorecard = _scorecard_payload(evidence_payload)
    if scorecard is None:
        return None, f"{SCORECARD_PATH}:missing"
    rows = scorecard.get("rows")
    if not isinstance(rows, list):
        return None, f"{SCORECARD_PATH}:missing"
    if not all(isinstance(row, Mapping) for row in rows):
        return None, f"{SCORECARD_PATH}:malformed-row"
    if len(rows) != len(QUALITY_SCORECARD_METRICS):
        return None, f"{SCORECARD_PATH}:metric-count"
    metrics = [row.get("metric") for row in rows]
    if metrics != list(QUALITY_SCORECARD_METRICS):
        return None, f"{SCORECARD_PATH}:metric-set"
    return all(row.get("status") == "ready" for row in rows), None


def _net_positive_from_projection(evidence_payload: Mapping[str, Any]) -> bool:
    try:
        projection = project_certificate_guided_claim(evidence_payload)
    except (KeyError, TypeError, ValueError):
        return False
    main = projection.main_verdict
    return (
        projection.main_claim_status == POSITIVE_STATUS
        and main.get("positive_discovery") is True
        and float(main.get("net_information", 0.0)) > 0.0
    )


def _merge_rejection(basis: dict[str, Any], decision: Mapping[str, Any]) -> None:
    evidence = decision.get("evidence_basis")
    if isinstance(evidence, Mapping):
        for key in (
            "malformed_detail",
            "source_schema_id",
            "source_artifact",
            "record_roles",
            "main_pair",
            "baseline_pair",
            "paired_quality_q_ci",
            "training_claim_gate_keys",
            "main_claim_status",
            "claim_gate",
            "main_verdict",
            "main_surface_delta_count",
            "main_shift_information",
            "main_structural_discovery",
            "control_verdict",
            "control_surface_delta_count",
            "control_shift_information",
            "control_structural_discovery",
            "control_positive_discovery",
            "forbidden_claim_term_hits",
        ):
            if key in evidence:
                basis[key] = evidence[key]
    basis["rejected"] = decision.get("rejected")
    basis["rejection_reason"] = decision.get("reason")


def _merge_audit(basis: dict[str, Any], decision: Mapping[str, Any]) -> None:
    basis["audit_status"] = decision.get("audit_status")
    basis["recorded_status"] = decision.get("recorded_status")
    basis["recomputed_status"] = decision.get("recomputed_status")
    basis["audit_reason"] = decision.get("reason")


def _merge_revocation(basis: dict[str, Any], decision: Mapping[str, Any]) -> None:
    basis["downgraded"] = decision.get("downgraded")
    basis["old_status"] = decision.get("old_status")
    basis["new_status"] = decision.get("new_status")
    basis["revocation_reason"] = decision.get("reason")
    delta = decision.get("evidence_delta")
    if isinstance(delta, Mapping):
        basis["quality_q_ci95_low"] = delta.get("quality_q_ci95_low")
        basis["paired_ci_status"] = delta.get("paired_ci_status")
        basis["audit_improvement_tradeoff"] = delta.get("audit_improvement_tradeoff")
        blockers = delta.get("blockers")
        basis["blockers"] = list(blockers) if isinstance(blockers, list) else []
    row = decision.get("ledger_row")
    if isinstance(row, Mapping):
        event = row.get("event")
        basis["ledger_row_event"] = event if isinstance(event, str) else None


def synthesize_certification_verdict(
    certificate_payload: Mapping[str, Any] | None,
    evidence_payload: Mapping[str, Any],
    *,
    timestamp_iso: str,
) -> dict[str, Any]:
    scorecard_ready, scorecard_detail = _scorecard_readiness(evidence_payload)
    rejection_decision = reject_certified_claim(
        certificate_payload,
        evidence_payload,
        timestamp_iso=timestamp_iso,
    )
    audit_decision = audit_certified_claim(
        certificate_payload,
        evidence_payload,
        timestamp_iso=timestamp_iso,
    )
    revocation_decision = reevaluate_certified_claim(
        certificate_payload,
        {
            "main_claim_status": audit_decision.get("recomputed_status"),
            "claim_gate": rejection_decision.get("evidence_basis", {}).get("claim_gate"),
        },
        timestamp_iso=timestamp_iso,
    )

    basis = _empty_basis()
    _merge_rejection(basis, rejection_decision)
    _merge_audit(basis, audit_decision)
    _merge_revocation(basis, revocation_decision)
    basis["scorecard_ready"] = scorecard_ready is True
    basis["net_positive_signal"] = _net_positive_from_projection(evidence_payload)

    if scorecard_detail is not None:
        basis["malformed_detail"] = scorecard_detail
        return _decision(
            verdict=REJECTED,
            reason=MALFORMED_EVIDENCE,
            evidence_basis=basis,
            timestamp_iso=timestamp_iso,
        )

    if rejection_decision.get("rejected") is True:
        return _decision(
            verdict=REJECTED,
            reason=str(rejection_decision.get("reason")),
            evidence_basis=basis,
            timestamp_iso=timestamp_iso,
        )

    if revocation_decision.get("downgraded") is True:
        return _decision(
            verdict=DEMOTED,
            reason=str(revocation_decision.get("reason")),
            evidence_basis=basis,
            timestamp_iso=timestamp_iso,
        )

    if scorecard_ready is not True:
        return _decision(
            verdict=LEDGER_ONLY,
            reason="scorecard-not-ready",
            evidence_basis=basis,
            timestamp_iso=timestamp_iso,
        )

    if audit_decision.get("audit_status") != AUDIT_CONSISTENT:
        return _decision(
            verdict=LEDGER_ONLY,
            reason="audit-not-consistent",
            evidence_basis=basis,
            timestamp_iso=timestamp_iso,
        )

    if basis["net_positive_signal"] is True:
        return _decision(
            verdict=POSITIVE_DISCOVERY,
            reason="net-positive-signal",
            evidence_basis=basis,
            timestamp_iso=timestamp_iso,
        )

    return _decision(
        verdict=ACCEPTED,
        reason="accepted",
        evidence_basis=basis,
        timestamp_iso=timestamp_iso,
    )
