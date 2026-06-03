"""Package-local discovery-level projection for lab report payloads."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping


DiscoveryLevel = Literal["D0", "D1", "D2", "D3", "D4", "D5", "DN", "DR"]


@dataclass(frozen=True)
class ResearchDiscoveryVerdict:
    experiment_id: str
    terminal_verdict: str
    discovery_level: DiscoveryLevel
    reasons: tuple[str, ...]
    classifier_shift: bool
    net_information: float | None
    scorecard_ready: bool
    control_positive: bool | None
    audit_status: str | None
    revocation_status: str | None


def _string_value(value: Any, default: str = "") -> str:
    return value if isinstance(value, str) else default


def _optional_string(value: Any) -> str | None:
    return value if isinstance(value, str) else None


def _bool_flag(payload: Mapping[str, Any], key: str) -> bool:
    return payload.get(key) is True


def _optional_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _float_or_none(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _first_mapping(payload: Mapping[str, Any], key: str) -> Mapping[str, Any] | None:
    value = payload.get(key)
    return value if isinstance(value, Mapping) else None


def _control_positive(payload: Mapping[str, Any]) -> bool | None:
    direct = _optional_bool(payload.get("control_positive"))
    if direct is not None:
        return direct

    basis = _first_mapping(payload, "evidence_basis")
    if basis is not None:
        basis_value = _optional_bool(basis.get("control_positive_discovery"))
        if basis_value is not None:
            return basis_value

    return _optional_bool(payload.get("control_positive_discovery"))


def _audit_improvement(payload: Mapping[str, Any]) -> bool:
    if payload.get("audit_improvement") is True:
        return True
    if payload.get("audit_improvement_tradeoff") is True:
        return True
    claim_gate = _first_mapping(payload, "claim_gate")
    if claim_gate is not None and claim_gate.get("training_audit_improvement_tradeoff") is True:
        return True
    return payload.get("training_audit_improvement_tradeoff") is True


def _debt_delta(payload: Mapping[str, Any]) -> float:
    value = _float_or_none(payload.get("debt_delta"))
    return 0.0 if value is None else value


def _assign_level(payload: Mapping[str, Any], terminal_verdict: str) -> tuple[DiscoveryLevel, tuple[str, ...]]:
    if payload.get("revoked") is True:
        return "DR", ("revoked=true",)
    if terminal_verdict in {"rejected", "demoted"}:
        return "DN", (f"terminal_verdict={terminal_verdict}",)
    if payload.get("positive_discovery") is True:
        if payload.get("robustness_passed") is True:
            return "D5", ("positive_discovery=true", "robustness_passed=true")
        return "D4", ("positive_discovery=true", "robustness_passed!=true")
    if payload.get("certified_discovery") is True:
        return "D3", ("certified_discovery=true",)
    if payload.get("classifier_shift") is True:
        return "D2", ("classifier_shift=true",)
    if _debt_delta(payload) < 0.0:
        return "D1", ("debt_delta<0",)
    if _audit_improvement(payload):
        return "D1", ("audit_improvement=true",)
    return "D0", ("no classifier shift or debt improvement",)


def assign_discovery_level(payload: Mapping[str, Any]) -> ResearchDiscoveryVerdict:
    """Project a lab payload onto D0-D5/DN/DR without defining a report schema.

    The projector reads canonical report keys directly. Existing verdict payloads
    use ``control_positive_discovery`` in ``evidence_basis``; this maps to the
    verdict's ``control_positive`` field. Existing certificate-guided claim gates
    use ``training_audit_improvement_tradeoff`` under ``claim_gate``; this maps
    to the D1 ``audit_improvement`` branch.
    """

    terminal_verdict = _string_value(payload.get("terminal_verdict"))
    level, reasons = _assign_level(payload, terminal_verdict)
    net_information = _float_or_none(payload.get("net_information"))
    return ResearchDiscoveryVerdict(
        experiment_id=_string_value(payload.get("experiment_id")),
        terminal_verdict=terminal_verdict,
        discovery_level=level,
        reasons=reasons,
        classifier_shift=_bool_flag(payload, "classifier_shift"),
        net_information=net_information,
        scorecard_ready=_bool_flag(payload, "scorecard_ready"),
        control_positive=_control_positive(payload),
        audit_status=_optional_string(payload.get("audit_status")),
        revocation_status=_optional_string(payload.get("revocation_status")),
    )
