from bedc_quality_lab import rejection
from bedc_quality_lab.schema import SCHEMA_ID
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


def _payload():
    payload = training_runner._payload()
    payload["schema_id"] = SCHEMA_ID
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


def _make_unresolved_control(payload):
    _copy_metric_role(payload, source_role="before", target_role="control")
    payload["deltas"]["control_minus_before"] = {
        key: 0.0 for key in payload["deltas"]["control_minus_before"]
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


def test_rejects_missing_or_wrong_schema_as_malformed_evidence():
    missing = _payload()
    del missing["schema_id"]
    missing_decision = rejection.reject_certified_claim(None, missing, timestamp_iso=TIMESTAMP)

    assert missing_decision["rejected"] is True
    assert missing_decision["reason"] == "malformed-evidence"
    assert missing_decision["evidence_basis"]["malformed_detail"] == "missing-schema-id"

    wrong = _payload()
    wrong["schema_id"] = "bedc-quality-lab:other-envelope"
    wrong_decision = rejection.reject_certified_claim(None, wrong, timestamp_iso=TIMESTAMP)

    assert wrong_decision["rejected"] is True
    assert wrong_decision["reason"] == "malformed-evidence"
    assert wrong_decision["evidence_basis"]["malformed_detail"] == "schema-id-mismatch"
    assert wrong_decision["evidence_basis"]["source_schema_id"] == "bedc-quality-lab:other-envelope"


def test_rejects_projection_source_failure_as_malformed_evidence():
    evidence = _payload()
    del evidence["claim_gate"]
    decision = rejection.reject_certified_claim(None, evidence, timestamp_iso=TIMESTAMP)

    assert decision["rejected"] is True
    assert decision["reason"] == "malformed-evidence"
    assert decision["evidence_basis"]["malformed_detail"].startswith("projection-unavailable:")


def test_rejects_missing_projection_fields_as_malformed_evidence(monkeypatch):
    class PartialProjection:
        def to_dict(self):
            return {
                "main_claim_status": "mixed",
                "claim_gate": {},
            }

    monkeypatch.setattr(rejection, "project_certificate_guided_claim", lambda _payload: PartialProjection())
    decision = rejection.reject_certified_claim(None, _payload(), timestamp_iso=TIMESTAMP)

    assert decision["rejected"] is True
    assert decision["reason"] == "malformed-evidence"
    assert (
        decision["evidence_basis"]["malformed_detail"]
        == "projection-fields-missing:main_verdict,matched_random_baseline,evidence_basis"
    )


def test_rejects_when_main_classifier_shift_is_absent():
    evidence = _payload()
    _make_no_main_shift(evidence)
    decision = rejection.reject_certified_claim(None, evidence, timestamp_iso=TIMESTAMP)

    assert decision["rejected"] is True
    assert decision["reason"] == "no-classifier-shift"
    assert decision["evidence_basis"]["main_surface_delta_count"] == 0
    assert decision["evidence_basis"]["main_shift_information"] == 0


def test_rejects_when_control_is_unresolved():
    evidence = _payload()
    _make_positive_main(evidence)
    _make_unresolved_control(evidence)
    decision = rejection.reject_certified_claim(None, evidence, timestamp_iso=TIMESTAMP)

    assert decision["rejected"] is True
    assert decision["reason"] == "control-unresolved"
    assert decision["evidence_basis"]["control_surface_delta_count"] == 0
    assert decision["evidence_basis"]["control_shift_information"] == 0
    assert decision["evidence_basis"]["control_positive_discovery"] is False


def test_rejects_when_control_is_positive():
    evidence = _payload()
    _make_positive_main(evidence)
    _make_positive_control(evidence)
    decision = rejection.reject_certified_claim(None, evidence, timestamp_iso=TIMESTAMP)

    assert decision["rejected"] is True
    assert decision["reason"] == "control-unresolved"
    assert decision["evidence_basis"]["control_verdict"] == "positive"
    assert decision["evidence_basis"]["control_positive_discovery"] is True


def test_rejects_forbidden_positive_claim_term_from_shared_owner():
    evidence = _payload()
    _make_positive_main(evidence)
    decision = rejection.reject_certified_claim(
        {"main_claim_status": "positive", "claim": "full-lejepa certification"},
        evidence,
        timestamp_iso=TIMESTAMP,
    )

    assert decision["rejected"] is True
    assert decision["reason"] == "overclaim"
    assert decision["evidence_basis"]["forbidden_claim_term_hits"] == ["full-lejepa"]


def test_clean_certificate_guided_claim_is_not_rejected():
    evidence = _payload()
    _make_positive_main(evidence)
    decision = rejection.reject_certified_claim(
        {"main_claim_status": "positive", "claim": "certificate-guided scoped quality improvement"},
        evidence,
        timestamp_iso=TIMESTAMP,
    )

    assert decision["rejected"] is False
    assert decision["reason"] == "not-rejected"
    assert decision["evidence_basis"]["main_claim_status"] == "positive"
    assert decision["evidence_basis"]["main_shift_information"] > 0
    assert decision["evidence_basis"]["control_verdict"] == "negative"
    assert decision["evidence_basis"]["forbidden_claim_term_hits"] == []


def test_rejection_decision_preserves_caller_timestamp_and_has_no_report_schema_keys():
    evidence = _payload()
    _make_positive_main(evidence)
    decision = rejection.reject_certified_claim(None, evidence, timestamp_iso=TIMESTAMP)

    assert decision["decided_at"] == TIMESTAMP
    assert "report_schema_id" not in decision
    assert "report_kind" not in decision
    assert "report_schema_id" not in decision["evidence_basis"]
    assert "report_kind" not in decision["evidence_basis"]
