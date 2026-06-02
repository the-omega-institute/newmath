from bedc_quality_lab import audit
from bedc_quality_lab.claim_projection import project_certificate_guided_claim
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_certificate_guided_training as training_runner


TIMESTAMP = "2026-06-03T00:00:00+00:00"


def _payload():
    payload = training_runner._payload()
    payload["schema_id"] = SCHEMA_ID
    return payload


def _role_records(payload, role):
    return [record for record in payload["records"] if record["role"] == role]


def _make_positive(payload):
    payload["claim_gate"]["positive_quality_improvement"] = True
    payload["claim_gate"]["quality_q_ci95_low"] = 0.1
    payload["claim_gate"]["paired_ci_status"] = "ok"
    payload["claim_gate"]["audit_improvement_tradeoff"] = False
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["status"] = "ok"
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["ci95_low"] = 0.1
    sources = {record["seed"]: record for record in _role_records(payload, "before")}
    for target in _role_records(payload, "after"):
        source = sources[target["seed"]]
        for name in (
            "quality_q",
            "quality_benefit",
            "quality_cost",
            "quality_debt",
            "certificate_guided_loss",
            "unlogged_error_rate",
            "critical_unlogged_error_rate",
        ):
            target[name] = source[name] + 0.25
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = -1.0


def test_audit_consistent_when_recorded_status_matches_recomputed_status():
    evidence = _payload()
    recorded = project_certificate_guided_claim(evidence).main_claim_status
    decision = audit.audit_certified_claim(
        {"main_claim_status": recorded},
        evidence,
        timestamp_iso=TIMESTAMP,
    )

    assert decision["audit_status"] == "consistent"
    assert decision["recorded_status"] == recorded
    assert decision["recomputed_status"] == recorded
    assert decision["reason"] == "recorded-status-matches-recomputed-status"


def test_audit_divergent_when_positive_recorded_but_evidence_recomputes_nonpositive():
    evidence = _payload()
    decision = audit.audit_certified_claim(
        {"main_claim_status": "positive"},
        evidence,
        timestamp_iso=TIMESTAMP,
    )

    assert decision["audit_status"] == "divergent"
    assert decision["recorded_status"] == "positive"
    assert decision["recomputed_status"] != "positive"
    assert decision["reason"] == "recorded-status-differs-from-recomputed-status"


def test_audit_divergent_when_recorded_nonpositive_but_evidence_recomputes_positive():
    evidence = _payload()
    _make_positive(evidence)
    decision = audit.audit_certified_claim(
        {"main_claim_status": "mixed"},
        evidence,
        timestamp_iso=TIMESTAMP,
    )

    assert decision["audit_status"] == "divergent"
    assert decision["recorded_status"] == "mixed"
    assert decision["recomputed_status"] == "positive"
    assert decision["reason"] == "recorded-status-differs-from-recomputed-status"


def test_audit_unverifiable_when_schema_id_missing_or_wrong():
    missing = _payload()
    del missing["schema_id"]
    missing_decision = audit.audit_certified_claim(
        {"main_claim_status": "mixed"},
        missing,
        timestamp_iso=TIMESTAMP,
    )
    assert missing_decision["audit_status"] == "unverifiable"
    assert missing_decision["reason"] == "missing-schema-id"

    wrong = _payload()
    wrong["schema_id"] = "bedc-quality-lab:other-envelope"
    wrong_decision = audit.audit_certified_claim(
        {"main_claim_status": "mixed"},
        wrong,
        timestamp_iso=TIMESTAMP,
    )
    assert wrong_decision["audit_status"] == "unverifiable"
    assert wrong_decision["reason"] == "schema-id-mismatch"


def test_audit_unverifiable_when_projection_fields_are_missing(monkeypatch):
    class PartialProjection:
        def to_dict(self):
            return {
                "main_claim_status": "mixed",
                "claim_gate": {},
            }

    monkeypatch.setattr(audit, "project_certificate_guided_claim", lambda _payload: PartialProjection())
    decision = audit.audit_certified_claim(
        {"main_claim_status": "mixed"},
        _payload(),
        timestamp_iso=TIMESTAMP,
    )

    assert decision["audit_status"] == "unverifiable"
    assert decision["recomputed_status"] is None
    assert decision["reason"] == "projection-fields-missing:main_verdict,matched_random_baseline,evidence_basis"


def test_audit_row_preserves_caller_timestamp_and_evidence_basis():
    evidence = _payload()
    decision = audit.audit_certified_claim(
        {"main_claim_status": "mixed"},
        evidence,
        timestamp_iso=TIMESTAMP,
    )

    assert decision["audit_row"]["timestamp"] == TIMESTAMP
    assert decision["audit_row"]["event"] == "certified-claim-audit"
    assert decision["audit_row"]["evidence_basis"] == decision["evidence_basis"]
    assert decision["evidence_basis"]["source_schema_id"] == SCHEMA_ID
    assert decision["evidence_basis"]["main_pair"] == ["before", "after"]
