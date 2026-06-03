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


def _first_list(payload: Mapping[str, Any], key: str) -> list[Any] | None:
    value = payload.get(key)
    return value if isinstance(value, list) else None


def _first_verdict_row(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    direct = _first_mapping(payload, "main_verdict")
    if direct is not None:
        return direct

    if "shift_information" in payload and "structural_discovery" in payload:
        return payload

    basis = _first_mapping(payload, "evidence_basis")
    if basis is not None:
        nested = _first_mapping(basis, "main_verdict")
        if nested is not None:
            return nested

    verdicts = _first_list(payload, "verdicts")
    if verdicts:
        first = verdicts[0]
        if isinstance(first, Mapping):
            return first

    return None


def _claim_gate(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    direct = _first_mapping(payload, "claim_gate")
    if direct is not None:
        return direct
    basis = _first_mapping(payload, "evidence_basis")
    if basis is not None:
        return _first_mapping(basis, "claim_gate")
    return None


def _revocation_decision(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    direct = _first_mapping(payload, "revocation_decision")
    if direct is not None:
        return direct
    basis = _first_mapping(payload, "evidence_basis")
    if basis is not None and any(key in basis for key in ("downgraded", "old_status", "new_status", "revocation_reason")):
        return basis
    return None


def _certificate_status(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    direct = _first_mapping(payload, "certificate_status")
    if direct is not None:
        return direct
    return _first_mapping(payload, "status_resolution")


def _terminal_verdict(payload: Mapping[str, Any]) -> str:
    return _string_value(payload.get("verdict"))


def _positive_discovery(payload: Mapping[str, Any], main: Mapping[str, Any] | None) -> bool:
    if main is not None and main.get("positive_discovery") is True:
        return True
    if payload.get("positive_discovery") is True:
        return True
    treatment = _first_mapping(payload, "treatment_verdict")
    return treatment is not None and treatment.get("positive") is True


def _has_robustness_report_pass(payload: Mapping[str, Any]) -> bool:
    gates = _first_mapping(payload, "acceptance_gates")
    if gates is not None and gates.get("status") != "pass":
        return False
    return payload.get("final_status") == "pass" and gates is not None


def _classifier_shift(main: Mapping[str, Any] | None) -> bool:
    if main is None:
        return False
    surface = _float_or_none(main.get("surface_delta_count"))
    shift = _float_or_none(main.get("shift_information"))
    return (surface is not None and surface > 0.0) and (shift is not None and shift > 0.0)


def _structural_discovery(main: Mapping[str, Any] | None) -> bool:
    return main is not None and main.get("structural_discovery") is True and _classifier_shift(main)


def _control_positive(payload: Mapping[str, Any]) -> bool | None:
    basis = _first_mapping(payload, "evidence_basis")
    if basis is not None:
        basis_value = _optional_bool(basis.get("control_positive_discovery"))
        if basis_value is not None:
            return basis_value

    baseline = _first_mapping(payload, "matched_random_baseline")
    if baseline is not None:
        baseline_value = _optional_bool(baseline.get("positive_discovery"))
        if baseline_value is not None:
            return baseline_value

    matched = _first_mapping(payload, "matched_random_control")
    if matched is not None:
        matched_verdict = _first_mapping(matched, "control_verdict")
        if matched_verdict is not None:
            matched_value = _optional_bool(matched_verdict.get("positive"))
            if matched_value is not None:
                return matched_value
        matched_projection = _first_mapping(matched, "control_projection")
        if matched_projection is not None:
            matched_value = _optional_bool(matched_projection.get("positive_discovery"))
            if matched_value is not None:
                return matched_value

    control = _first_mapping(payload, "control_verdict")
    if control is not None:
        return _optional_bool(control.get("positive"))

    return None


def _audit_improvement(payload: Mapping[str, Any]) -> bool:
    claim_gate = _first_mapping(payload, "claim_gate")
    if claim_gate is not None and claim_gate.get("training_audit_improvement_tradeoff") is True:
        return True
    basis = _first_mapping(payload, "evidence_basis")
    if basis is not None and basis.get("audit_improvement_tradeoff") is True:
        return True
    gate = _claim_gate(payload)
    return gate is not None and gate.get("training_audit_improvement_tradeoff") is True


def _debt_delta(main: Mapping[str, Any] | None) -> float:
    deltas = _first_mapping(main, "deltas") if main is not None else None
    value = _float_or_none(deltas.get("debt_delta")) if deltas is not None else None
    return 0.0 if value is None else value


def _revocation_status(payload: Mapping[str, Any]) -> str | None:
    cert_status = _certificate_status(payload)
    if cert_status is not None and cert_status.get("status") == "revoked":
        return "revoked"
    revocation = _revocation_decision(payload)
    if revocation is not None:
        return _optional_string(revocation.get("new_status"))
    return None


def _revocation_signal(payload: Mapping[str, Any]) -> tuple[bool, str | None]:
    cert_status = _certificate_status(payload)
    if cert_status is not None and cert_status.get("status") == "revoked":
        return True, "certificate_status.status=revoked"

    revocation = _revocation_decision(payload)
    if revocation is None:
        return False, None
    if revocation.get("downgraded") is True:
        return True, "revocation_decision.downgraded=true"
    new_status = _optional_string(revocation.get("new_status"))
    if new_status == "revoked":
        return True, f"revocation_decision.new_status={new_status}"
    return False, None


def _net_information(payload: Mapping[str, Any], main: Mapping[str, Any] | None) -> float | None:
    if main is not None:
        main_value = _float_or_none(main.get("net_information"))
        if main_value is not None:
            return main_value
    return _float_or_none(payload.get("net_information"))


def _scorecard_ready(payload: Mapping[str, Any]) -> bool:
    basis = _first_mapping(payload, "evidence_basis")
    return basis is not None and basis.get("scorecard_ready") is True


def _audit_status(payload: Mapping[str, Any]) -> str | None:
    basis = _first_mapping(payload, "evidence_basis")
    if basis is not None:
        basis_value = _optional_string(basis.get("audit_status"))
        if basis_value is not None:
            return basis_value
    audit = _first_mapping(payload, "audit_decision")
    if audit is not None:
        return _optional_string(audit.get("audit_status"))
    return None


def _experiment_id(payload: Mapping[str, Any]) -> str:
    for key in ("artifact", "json_artifact"):
        value = payload.get(key)
        if isinstance(value, str):
            return value
    return ""


def _assign_level(
    payload: Mapping[str, Any],
    terminal_verdict: str,
    main: Mapping[str, Any] | None,
) -> tuple[DiscoveryLevel, tuple[str, ...]]:
    revoked_signal, revocation_reason = _revocation_signal(payload)
    if revoked_signal:
        return "DR", (revocation_reason or "revocation signal present",)
    if terminal_verdict in {"rejected", "demoted"}:
        return "DN", (f"verdict={terminal_verdict}",)
    if _positive_discovery(payload, main):
        if _has_robustness_report_pass(payload):
            return "D5", ("positive_discovery=true", "acceptance_gates.status=pass", "final_status=pass")
        return "D4", ("positive_discovery=true", "robustness evidence absent")
    if _structural_discovery(main):
        return "D3", ("main_verdict.structural_discovery=true", "main_verdict.shift_information>0")
    if _classifier_shift(main):
        return "D2", ("main_verdict.surface_delta_count>0", "main_verdict.shift_information>0")
    if _debt_delta(main) < 0.0:
        return "D1", ("main_verdict.deltas.debt_delta<0",)
    if _audit_improvement(payload):
        return "D1", ("claim_gate.training_audit_improvement_tradeoff=true",)
    return "D0", ("no classifier shift or debt improvement",)


def assign_discovery_level(payload: Mapping[str, Any]) -> ResearchDiscoveryVerdict:
    """Project a lab payload onto D0-D5/DN/DR without defining a report schema.

    The projector reads existing lab report and projection keys directly:
    top-level ``verdict`` for terminal decisions; ``evidence_basis`` for verdict
    basis fields; ``main_verdict`` or canonical ``verdicts[0]`` for projection
    rows; ``claim_gate`` for audit tradeoff evidence; ``revocation_decision`` or
    certificate status for revocation evidence. D5 only accepts the real
    gap-head robustness report markers ``acceptance_gates.status`` and
    ``final_status`` when they accompany a positive discovery payload.
    """

    main = _first_verdict_row(payload)
    terminal_verdict = _terminal_verdict(payload)
    level, reasons = _assign_level(payload, terminal_verdict, main)
    return ResearchDiscoveryVerdict(
        experiment_id=_experiment_id(payload),
        terminal_verdict=terminal_verdict,
        discovery_level=level,
        reasons=reasons,
        classifier_shift=_classifier_shift(main),
        net_information=_net_information(payload, main),
        scorecard_ready=_scorecard_ready(payload),
        control_positive=_control_positive(payload),
        audit_status=_audit_status(payload),
        revocation_status=_revocation_status(payload),
    )
