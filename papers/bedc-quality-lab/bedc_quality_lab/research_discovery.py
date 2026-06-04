"""Package-local discovery-level projection for lab report payloads."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping


DiscoveryLevel = Literal["D0", "D1", "D2", "D3", "D4", "D5-O", "D5-M", "DN", "DR"]


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


@dataclass(frozen=True)
class DiscoveryGateBasis:
    classifier_shift: bool
    positive_net: bool
    control_negative: bool
    scorecard_ready: bool
    robustness_ready: bool
    mechanism_ready: bool
    terminal_failed: bool
    revoked: bool
    positive_terminal: bool
    source_pointers: Mapping[str, str]
    failed_gate_reasons: tuple[str, ...]


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


def _positive_net_signal(payload: Mapping[str, Any], main: Mapping[str, Any] | None) -> bool:
    for source in (payload, main, _first_mapping(payload, "evidence_basis")):
        if source is not None and source.get("net_positive_signal") is True:
            return True
    return False


def _has_robustness_report_pass(payload: Mapping[str, Any]) -> bool:
    gates = _first_mapping(payload, "acceptance_gates")
    if gates is not None and gates.get("status") != "pass":
        return False
    return payload.get("final_status") == "pass" and gates is not None


def _mechanism_attribution_all_pass(payload: Mapping[str, Any]) -> bool:
    mechanism_status = _optional_string(payload.get("mechanism_status"))
    if mechanism_status == "probe-margin-channel":
        return False

    mechanism_gate = _first_mapping(payload, "mechanism_attribution")
    if mechanism_gate is not None:
        if mechanism_gate.get("channel") == "probe-margin-channel":
            return False
        if mechanism_gate.get("status") in {"blocked", "failed"}:
            return False
        if mechanism_gate.get("failed_gate") is not None:
            return False
        if mechanism_gate.get("all_pass") is True:
            return True

    d5_target = _first_mapping(payload, "D5_target")
    mechanism_target = _first_mapping(d5_target, "mechanism") if d5_target is not None else None
    if mechanism_target is not None:
        if mechanism_target.get("status") in {"blocked", "failed"}:
            return False
        if mechanism_target.get("failed_gate") is not None:
            return False
        if mechanism_target.get("passed") is True:
            return True

    d5_m = _first_mapping(payload, "d5_m")
    if d5_m is not None:
        if d5_m.get("status") in {"blocked", "failed"}:
            return False
        if d5_m.get("failed_gate") is not None:
            return False
        if d5_m.get("passed") is True:
            return True

    attribution_gates = _first_list(payload, "mechanism_attribution_gates")
    if attribution_gates is not None:
        statuses = [row.get("status") for row in attribution_gates if isinstance(row, Mapping)]
        return bool(statuses) and all(status == "pass" for status in statuses)

    return False


def _source_pointers(payload: Mapping[str, Any]) -> dict[str, str]:
    result: dict[str, str] = {}
    direct = _first_mapping(payload, "source_pointers")
    if direct is not None:
        for key, value in direct.items():
            if isinstance(key, str) and isinstance(value, str) and value:
                result[key] = value
    for source_key, pointer_key in (
        ("operational_pointer", "operational"),
        ("mechanism_pointer", "mechanism"),
        ("mechanism_case_pointer", "mechanism_case"),
    ):
        value = payload.get(source_key)
        if isinstance(value, str) and value:
            result[pointer_key] = value
    return result


def _mechanism_ready(payload: Mapping[str, Any], source_pointers: Mapping[str, str]) -> bool:
    required = {"operational", "mechanism", "mechanism_case"}
    return required <= set(source_pointers) and _mechanism_attribution_all_pass(payload)


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


def _d4_failed_gate_reasons(basis: DiscoveryGateBasis) -> tuple[str, ...]:
    reasons: list[str] = []
    if not basis.positive_terminal:
        reasons.append("positive_terminal=false")
    if not basis.classifier_shift:
        reasons.append("classifier_shift=false")
    if not basis.positive_net:
        reasons.append("net_positive_signal=false")
    if not basis.control_negative:
        reasons.append("control_negative=false")
    if not basis.scorecard_ready:
        reasons.append("scorecard_ready=false")
    return tuple(reasons)


def _build_discovery_gate_basis(
    payload: Mapping[str, Any],
    terminal_verdict: str,
    main: Mapping[str, Any] | None,
) -> DiscoveryGateBasis:
    revoked, revocation_reason = _revocation_signal(payload)
    terminal_failed = terminal_verdict in {"rejected", "demoted"} or terminal_verdict.startswith("DN(")
    source_pointers = _source_pointers(payload)
    positive_terminal = _positive_discovery(payload, main)
    provisional = DiscoveryGateBasis(
        classifier_shift=_classifier_shift(main),
        positive_net=_positive_net_signal(payload, main),
        control_negative=_control_positive(payload) is False,
        scorecard_ready=_scorecard_ready(payload),
        robustness_ready=_has_robustness_report_pass(payload),
        mechanism_ready=_mechanism_ready(payload, source_pointers),
        terminal_failed=terminal_failed,
        revoked=revoked,
        positive_terminal=positive_terminal,
        source_pointers=source_pointers,
        failed_gate_reasons=(),
    )
    failed_reasons = _d4_failed_gate_reasons(provisional)
    if revoked and revocation_reason is not None:
        failed_reasons = (revocation_reason, *failed_reasons)
    return DiscoveryGateBasis(
        classifier_shift=provisional.classifier_shift,
        positive_net=provisional.positive_net,
        control_negative=provisional.control_negative,
        scorecard_ready=provisional.scorecard_ready,
        robustness_ready=provisional.robustness_ready,
        mechanism_ready=provisional.mechanism_ready,
        terminal_failed=provisional.terminal_failed,
        revoked=provisional.revoked,
        positive_terminal=provisional.positive_terminal,
        source_pointers=provisional.source_pointers,
        failed_gate_reasons=failed_reasons,
    )


def _assign_level(
    payload: Mapping[str, Any],
    terminal_verdict: str,
    basis: DiscoveryGateBasis,
    main: Mapping[str, Any] | None,
) -> tuple[DiscoveryLevel, tuple[str, ...]]:
    if basis.revoked:
        reason = basis.failed_gate_reasons[0] if basis.failed_gate_reasons else "revocation signal present"
        return "DR", (reason,)
    if basis.terminal_failed:
        return "DN", (f"verdict={terminal_verdict}",)
    d4_pass = (
        basis.positive_terminal
        and basis.classifier_shift
        and basis.positive_net
        and basis.control_negative
        and basis.scorecard_ready
    )
    if basis.positive_terminal and not d4_pass:
        return "DN", basis.failed_gate_reasons
    if d4_pass and basis.robustness_ready and basis.mechanism_ready:
        return (
            "D5-M",
            (
                "positive_terminal=true",
                "classifier_shift=true",
                "net_positive_signal=true",
                "control_negative=true",
                "scorecard_ready=true",
                "robustness_ready=true",
                "mechanism_ready=true",
            ),
        )
    if d4_pass and basis.robustness_ready:
        return (
            "D5-O",
            (
                "positive_terminal=true",
                "classifier_shift=true",
                "net_positive_signal=true",
                "control_negative=true",
                "scorecard_ready=true",
                "robustness_ready=true",
                "mechanism_ready=false",
            ),
        )
    if d4_pass:
        return (
            "D4",
            (
                "positive_terminal=true",
                "classifier_shift=true",
                "net_positive_signal=true",
                "control_negative=true",
                "scorecard_ready=true",
                "robustness_ready=false",
            ),
        )
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
    """Project a lab payload onto discovery levels without defining a report schema.

    The projector reads existing lab report and projection keys directly:
    top-level ``verdict`` for terminal decisions; ``evidence_basis`` for verdict
    basis fields; ``main_verdict`` or canonical ``verdicts[0]`` for projection
    rows; ``claim_gate`` for audit tradeoff evidence; ``revocation_decision`` or
    certificate status for revocation evidence. Operational closure accepts the
    real gap-head robustness report markers ``acceptance_gates.status`` and
    ``final_status`` when they accompany a positive discovery payload; mechanism
    closure additionally requires attribution gates to pass.
    """

    main = _first_verdict_row(payload)
    terminal_verdict = _terminal_verdict(payload)
    basis = _build_discovery_gate_basis(payload, terminal_verdict, main)
    level, reasons = _assign_level(payload, terminal_verdict, basis, main)
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
