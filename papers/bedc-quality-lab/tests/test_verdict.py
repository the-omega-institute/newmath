import json

from bedc_quality_lab.schema import SCHEMA_ID
from bedc_quality_lab.verdict import (
    QUALITY_SCORECARD_METRICS,
    synthesize_certification_verdict,
)
from scripts import run_certificate_guided_training as training_runner


TIMESTAMP = "2026-06-03T00:00:00+00:00"
METRIC_NAMES = (
    "quality_q",
    "quality_benefit",
    "quality_cost",
    "quality_debt",
    "certificate_guided_loss",
    "unlogged_error_rate",
    "critical_unlogged_error_rate",
)


def _scorecard_rows(status="ready"):
    return [{"metric": metric, "status": status, "value": index} for index, metric in enumerate(QUALITY_SCORECARD_METRICS)]


def _scorecard(status="ready"):
    return {
        "artifact_id": "bedc-quality-lab:quality-scorecard",
        "generated_at": TIMESTAMP,
        "rows": _scorecard_rows(status=status),
    }


def _payload(*, scorecard_status="ready"):
    payload = training_runner._payload()
    payload["schema_id"] = SCHEMA_ID
    payload["quality_scorecard"] = _scorecard(status=scorecard_status)
    return payload


def _role_records(payload, role):
    return [record for record in payload["records"] if record["role"] == role]


def _copy_metric_role(payload, *, source_role, target_role):
    sources = {record["seed"]: record for record in _role_records(payload, source_role)}
    for target in _role_records(payload, target_role):
        source = sources[target["seed"]]
        for name in METRIC_NAMES:
            target[name] = source[name]


def _make_positive_main(payload):
    payload["claim_gate"]["positive_quality_improvement"] = True
    payload["claim_gate"]["quality_q_ci95_low"] = 0.1
    payload["claim_gate"]["paired_ci_status"] = "ok"
    payload["claim_gate"]["audit_improvement_tradeoff"] = False
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["status"] = "ok"
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["ci95_low"] = 0.1
    sources = {record["seed"]: record for record in _role_records(payload, "before")}
    for target in _role_records(payload, "after"):
        source = sources[target["seed"]]
        for name in METRIC_NAMES:
            target[name] = source[name] + 0.25
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = -1.0


def _make_no_main_shift(payload):
    _copy_metric_role(payload, source_role="before", target_role="after")
    payload["deltas"]["after_minus_before"] = {
        key: 0.0 for key in payload["deltas"]["after_minus_before"]
    }


def _make_positive_control(payload):
    sources = {record["seed"]: record for record in _role_records(payload, "before")}
    for target in _role_records(payload, "control"):
        source = sources[target["seed"]]
        for name in METRIC_NAMES:
            target[name] = source[name] + 0.25
    payload["deltas"]["control_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["control_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["control_minus_before"]["debt_delta"] = -1.0


def _decide(certificate_payload, evidence_payload):
    return synthesize_certification_verdict(
        certificate_payload,
        evidence_payload,
        timestamp_iso=TIMESTAMP,
    )


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def test_accepted_when_consistent_ready_not_rejected_and_no_net_positive_signal():
    evidence = _payload()
    decision = _decide({"main_claim_status": "observed-negative"}, evidence)

    assert decision["verdict"] == "accepted"
    assert decision["reason"] == "accepted"
    assert decision["evidence_basis"]["audit_status"] == "consistent"
    assert decision["evidence_basis"]["rejected"] is False
    assert decision["evidence_basis"]["downgraded"] is False
    assert decision["evidence_basis"]["scorecard_ready"] is True
    assert decision["evidence_basis"]["net_positive_signal"] is False


def test_positive_discovery_requires_ready_scorecard_and_net_positive_signal():
    evidence = _payload()
    _make_positive_main(evidence)
    decision = _decide({"main_claim_status": "positive"}, evidence)

    assert decision["verdict"] == "positive-discovery"
    assert decision["reason"] == "net-positive-signal"
    assert decision["evidence_basis"]["main_claim_status"] == "positive"
    assert decision["evidence_basis"]["scorecard_ready"] is True
    assert decision["evidence_basis"]["net_positive_signal"] is True


def test_explicit_rejection_preempts_demoted_and_ledger_only():
    evidence = _payload(scorecard_status="not-ready")
    _make_no_main_shift(evidence)
    decision = _decide({"main_claim_status": "positive"}, evidence)

    assert decision["verdict"] == "rejected"
    assert decision["reason"] == "no-classifier-shift"
    assert decision["evidence_basis"]["rejected"] is True
    assert decision["evidence_basis"]["downgraded"] is True
    assert decision["evidence_basis"]["scorecard_ready"] is False


def test_demoted_preempts_ledger_only_when_not_rejected():
    evidence = _payload(scorecard_status="not-ready")
    decision = _decide({"main_claim_status": "positive"}, evidence)

    assert decision["verdict"] == "demoted"
    assert decision["reason"] == "audit-improvement-tradeoff"
    assert decision["evidence_basis"]["rejected"] is False
    assert decision["evidence_basis"]["downgraded"] is True
    assert decision["evidence_basis"]["ledger_row_event"] == "certified-claim-revocation"
    assert decision["evidence_basis"]["scorecard_ready"] is False


def test_well_formed_not_ready_scorecard_goes_to_ledger_only():
    evidence = _payload(scorecard_status="not-ready")
    decision = _decide({"main_claim_status": "observed-negative"}, evidence)

    assert decision["verdict"] == "ledger-only"
    assert decision["reason"] == "scorecard-not-ready"
    assert decision["evidence_basis"]["scorecard_ready"] is False
    assert decision["evidence_basis"]["rejected"] is False
    assert decision["evidence_basis"]["downgraded"] is False


def test_audit_not_consistent_goes_to_ledger_only_after_ready_gate():
    evidence = _payload()
    decision = _decide({"main_claim_status": "mixed"}, evidence)

    assert decision["verdict"] == "ledger-only"
    assert decision["reason"] == "audit-not-consistent"
    assert decision["evidence_basis"]["audit_status"] == "divergent"
    assert decision["evidence_basis"]["scorecard_ready"] is True


def test_malformed_scorecard_fails_closed_to_rejected():
    evidence = _payload()
    del evidence["quality_scorecard"]
    decision = _decide({"main_claim_status": "observed-negative"}, evidence)

    assert decision["verdict"] == "rejected"
    assert decision["reason"] == "malformed-evidence"
    assert decision["evidence_basis"]["malformed_detail"] == "$.quality_scorecard.rows:missing"
    assert decision["evidence_basis"]["scorecard_ready"] is False


def test_schema_malformed_evidence_fails_closed_to_rejected():
    evidence = _payload()
    del evidence["schema_id"]
    decision = _decide({"main_claim_status": "observed-negative"}, evidence)

    assert decision["verdict"] == "rejected"
    assert decision["reason"] == "malformed-evidence"
    assert decision["evidence_basis"]["malformed_detail"] == "missing-schema-id"
    assert decision["evidence_basis"]["scorecard_ready"] is True


def test_positive_discovery_does_not_pass_without_ready_scorecard():
    evidence = _payload(scorecard_status="not-ready")
    _make_positive_main(evidence)
    decision = _decide({"main_claim_status": "positive"}, evidence)

    assert decision["verdict"] == "ledger-only"
    assert decision["reason"] == "scorecard-not-ready"
    assert decision["evidence_basis"]["net_positive_signal"] is True
    assert decision["evidence_basis"]["scorecard_ready"] is False


def test_accepted_does_not_pass_with_malformed_scorecard_rows():
    evidence = _payload()
    evidence["quality_scorecard"]["rows"] = [{"metric": "CertCov", "status": "ready"}]
    decision = _decide({"main_claim_status": "observed-negative"}, evidence)

    assert decision["verdict"] == "rejected"
    assert decision["reason"] == "malformed-evidence"
    assert decision["evidence_basis"]["malformed_detail"] == "$.quality_scorecard.rows:metric-count"


def test_control_positive_rejection_is_terminal():
    evidence = _payload()
    _make_positive_main(evidence)
    _make_positive_control(evidence)
    decision = _decide({"main_claim_status": "positive"}, evidence)

    assert decision["verdict"] == "rejected"
    assert decision["reason"] == "control-unresolved"
    assert decision["evidence_basis"]["control_positive_discovery"] is True
    assert decision["evidence_basis"]["net_positive_signal"] is True


def test_caller_timestamp_is_preserved_and_report_schema_fields_are_absent():
    timestamp = "2030-01-02T03:04:05+00:00"
    decision = synthesize_certification_verdict(
        {"main_claim_status": "observed-negative"},
        _payload(),
        timestamp_iso=timestamp,
    )

    assert decision["decided_at"] == timestamp
    assert "report_schema_id" not in decision
    assert "report_kind" not in decision
    keys = set(_walk_keys(decision))
    assert "report_schema_id" not in keys
    assert "report_kind" not in keys


def test_evidence_basis_is_flat_and_contains_only_minimal_scorecard_signal():
    decision = _decide({"main_claim_status": "observed-negative"}, _payload())
    basis = decision["evidence_basis"]

    assert "signals" not in basis
    assert "derived" not in basis
    assert "scorecard_ready" in basis
    forbidden_scorecard_keys = {
        "rows",
        "quality_scorecard",
        "scorecard",
        "scorecard_ready_count",
        "scorecard_metric_count",
        "scorecard_not_ready_metrics",
        "scorecard_ready_metrics",
        "scorecard_artifact_id",
        "artifact_id",
    }
    assert not (forbidden_scorecard_keys & set(_walk_keys(basis)))
    assert not any(isinstance(value, dict) and "status" in value and "metric" in value for value in basis.values())
    json.dumps(decision)


def test_verdict_module_is_not_exported_from_package_all():
    import bedc_quality_lab

    assert "verdict" not in bedc_quality_lab.__all__
