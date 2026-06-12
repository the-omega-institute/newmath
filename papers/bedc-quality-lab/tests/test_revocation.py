from bedc_quality_lab.revocation import reevaluate_certified_claim


TIMESTAMP = "2026-06-03T00:00:00+00:00"
RETURN_KEYS = {
    "downgraded",
    "old_status",
    "new_status",
    "reason",
    "evidence_delta",
    "ledger_row",
}


def _fresh(status="positive", **gate):
    base_gate = {
        "training_quality_q_ci95_low": 0.25,
        "training_paired_ci_status": "ok",
        "training_audit_improvement_tradeoff": False,
        "positive_discovery_four_gate": status == "positive",
        "blockers": [],
    }
    base_gate.update(gate)
    return {
        "generated_at": TIMESTAMP,
        "main_claim_status": status,
        "claim_gate": base_gate,
    }


def _positive_certificate():
    return {
        "main_claim_status": "positive",
        "source_artifact": "reports/certificate_guided_discovery.json",
    }


def test_absent_certificate_produces_empty_ledger_without_downgrade():
    decision = reevaluate_certified_claim(None, _fresh(), timestamp_iso=TIMESTAMP)

    assert set(decision) == RETURN_KEYS
    assert decision["downgraded"] is False
    assert decision["old_status"] is None
    assert decision["new_status"] is None
    assert decision["reason"] == "no-certified-claim"
    assert decision["evidence_delta"] == {}
    assert decision["ledger_row"] == {}


def test_old_non_positive_certificate_has_no_status_to_downgrade():
    decision = reevaluate_certified_claim(
        {"main_claim_status": "mixed"},
        _fresh(),
        timestamp_iso=TIMESTAMP,
    )

    assert set(decision) == RETURN_KEYS
    assert decision["downgraded"] is False
    assert decision["old_status"] == "mixed"
    assert decision["new_status"] == "mixed"
    assert decision["reason"] == "old-certificate-not-positive"
    assert decision["ledger_row"] == {}


def test_stale_positive_with_nonpositive_ci_lower_downgrades_and_writes_ledger():
    decision = reevaluate_certified_claim(
        _positive_certificate(),
        _fresh(
            "observed-negative",
            training_quality_q_ci95_low=0.0,
            blockers=["quality-q-ci95-low-nonpositive"],
        ),
        timestamp_iso=TIMESTAMP,
    )

    assert set(decision) == RETURN_KEYS
    assert decision["downgraded"] is True
    assert decision["old_status"] == "positive"
    assert decision["new_status"] == "observed-negative"
    assert decision["reason"] == "paired-quality-ci-weakened"
    assert decision["evidence_delta"]["quality_q_ci95_low"] == 0.0
    assert decision["evidence_delta"]["blockers"] == ["quality-q-ci95-low-nonpositive"]
    assert decision["ledger_row"]["timestamp"] == TIMESTAMP
    assert decision["ledger_row"]["evidence_delta"] == decision["evidence_delta"]


def test_stale_positive_with_tradeoff_downgrades_to_tradeoff_status():
    decision = reevaluate_certified_claim(
        _positive_certificate(),
        _fresh(
            "mixed",
            training_audit_improvement_tradeoff=True,
            blockers=["audit-improvement-tradeoff"],
        ),
        timestamp_iso=TIMESTAMP,
    )

    assert decision["downgraded"] is True
    assert decision["new_status"] == "audit-improvement-tradeoff"
    assert decision["reason"] == "audit-improvement-tradeoff"
    assert decision["evidence_delta"]["audit_improvement_tradeoff"] is True
    assert decision["ledger_row"]["new_status"] == "audit-improvement-tradeoff"


def test_stale_positive_remains_when_fresh_projection_is_positive():
    decision = reevaluate_certified_claim(
        _positive_certificate(),
        _fresh("positive"),
        timestamp_iso=TIMESTAMP,
    )

    assert decision["downgraded"] is False
    assert decision["old_status"] == "positive"
    assert decision["new_status"] == "positive"
    assert decision["reason"] == "fresh-claim-remains-positive"
    assert decision["ledger_row"] == {}


def test_caller_timestamp_is_preserved_in_ledger_row():
    timestamp = "2030-01-02T03:04:05+00:00"
    decision = reevaluate_certified_claim(
        _positive_certificate(),
        _fresh("mixed", training_quality_q_ci95_low=-0.1),
        timestamp_iso=timestamp,
    )

    assert decision["downgraded"] is True
    assert decision["ledger_row"]["timestamp"] == timestamp


def test_malformed_fresh_gate_fails_closed():
    decision = reevaluate_certified_claim(
        _positive_certificate(),
        {"main_claim_status": "positive"},
        timestamp_iso=TIMESTAMP,
    )

    assert decision["downgraded"] is True
    assert decision["old_status"] == "positive"
    assert decision["new_status"] == "mixed"
    assert decision["reason"] == "malformed-fresh-claim-gate"
    assert decision["ledger_row"]["reason"] == "malformed-fresh-claim-gate"


def test_missing_fresh_ci_fields_fail_closed():
    decision = reevaluate_certified_claim(
        _positive_certificate(),
        {"main_claim_status": "positive", "claim_gate": {"blockers": []}},
        timestamp_iso=TIMESTAMP,
    )

    assert decision["downgraded"] is True
    assert decision["new_status"] == "mixed"
    assert decision["reason"] == "malformed-fresh-claim-gate"
