import pytest

from bedc_quality_lab.certification import issue_certification_record
from bedc_quality_lab.certification_ledger import (
    CERTIFICATION_LEDGER_ENTRY_KIND,
    CERTIFICATION_LEDGER_KIND,
    audit_certification_ledger,
    empty_certification_ledger,
    publish_certification_record,
)


ISSUED_AT = "2026-06-03T01:02:03+00:00"
PUBLISHED_AT = "2026-06-03T02:03:04+00:00"
SOURCE_REF = "reports/certificates/run-57.json#certificate"
LEDGER_SOURCE_REF = "reports/certification-ledger.json"


def _model_identity(**overrides):
    base = {
        "model_id": "bedc-quality-model",
        "model_version": "quality-2026-06-03",
        "classifier_id": "classifier-main",
        "scope_id": "scope-bedc-quality",
    }
    base.update(overrides)
    return base


def _verdict_decision(**overrides):
    base = {
        "verdict": "accepted",
        "reason": "accepted",
        "decided_at": "2026-06-03T00:00:00+00:00",
        "evidence_basis": {
            "audit_status": "consistent",
            "record_roles": ["before", "after", "control"],
            "scorecard_ready": True,
            "nested": {"quality_q_ci95_low": 0.25},
        },
    }
    base.update(overrides)
    return base


def _record(**overrides):
    return issue_certification_record(
        overrides.pop("model_identity", _model_identity()),
        overrides.pop("verdict_decision", _verdict_decision()),
        timestamp_iso=overrides.pop("timestamp_iso", ISSUED_AT),
        source_ref=overrides.pop("source_ref", SOURCE_REF),
        previous_certificate_id=overrides.pop("previous_certificate_id", None),
    )


def _publish(ledger, record, **overrides):
    return publish_certification_record(
        ledger,
        record,
        timestamp_iso=overrides.pop("timestamp_iso", PUBLISHED_AT),
        source_ref=overrides.pop("source_ref", LEDGER_SOURCE_REF),
    )


def test_empty_ledger_and_genesis_append_shape():
    ledger = empty_certification_ledger(source_ref=LEDGER_SOURCE_REF)
    record = _record()

    published = _publish(ledger, record)

    assert ledger == {
        "ledger_kind": CERTIFICATION_LEDGER_KIND,
        "source_ref": LEDGER_SOURCE_REF,
        "entries": [],
        "head_certificate_id": None,
        "head_entry_digest": None,
        "entry_count": 0,
    }
    assert published["ledger_kind"] == CERTIFICATION_LEDGER_KIND
    assert published["source_ref"] == LEDGER_SOURCE_REF
    assert published["entry_count"] == 1
    assert published["head_certificate_id"] == record["certificate_id"]
    assert published["head_entry_digest"] == published["entries"][0]["entry_digest"]
    assert audit_certification_ledger(published) == []


def test_linked_append_updates_head_and_back_pointers():
    first = _record()
    ledger = _publish(empty_certification_ledger(), first)
    second = _record(
        timestamp_iso="2026-06-03T03:04:05+00:00",
        previous_certificate_id=first["certificate_id"],
    )

    published = _publish(ledger, second, timestamp_iso="2026-06-03T04:05:06+00:00")

    first_entry, second_entry = published["entries"]
    assert published["entry_count"] == 2
    assert published["head_certificate_id"] == second["certificate_id"]
    assert first_entry["previous_certificate_id"] is None
    assert second_entry["previous_certificate_id"] == first["certificate_id"]
    assert second_entry["previous_entry_digest"] == first_entry["entry_digest"]
    assert audit_certification_ledger(published) == []


def test_publish_returns_immutable_copy_and_does_not_mutate_input():
    first = _record()
    ledger = _publish(empty_certification_ledger(), first)
    before = {
        **ledger,
        "entries": [dict(entry) for entry in ledger["entries"]],
    }

    copy = _publish(ledger, first)

    assert copy == ledger
    assert copy is not ledger
    assert copy["entries"] is not ledger["entries"]
    assert copy["entries"][0] is not ledger["entries"][0]
    copy["entries"][0]["source_ref"] = "reports/changed.json"
    assert ledger == before


def test_current_head_publish_is_idempotent():
    record = _record()
    ledger = _publish(empty_certification_ledger(), record)

    again = _publish(ledger, record)

    assert again == ledger
    assert len(again["entries"]) == 1


def test_stale_duplicate_and_fork_rejection():
    first = _record()
    ledger = _publish(empty_certification_ledger(), first)
    second = _record(
        timestamp_iso="2026-06-03T03:04:05+00:00",
        previous_certificate_id=first["certificate_id"],
    )
    ledger = _publish(ledger, second)
    sibling = _record(
        timestamp_iso="2026-06-03T05:06:07+00:00",
        source_ref="reports/certificates/sibling.json#certificate",
        previous_certificate_id=first["certificate_id"],
    )

    with pytest.raises(ValueError, match="already appears"):
        _publish(ledger, first)
    with pytest.raises(ValueError, match="discontinuity"):
        _publish(ledger, sibling)


def test_tampered_certificate_record_is_rejected():
    record = _record()
    tampered = dict(record)
    tampered["reason"] = "tampered"

    with pytest.raises(ValueError, match="certificate_id mismatch"):
        _publish(empty_certification_ledger(), tampered)


def test_publish_rejects_malformed_record_kind_ids_timestamp_source_and_ledger():
    record = _record()

    bad_kind = dict(record, record_kind="other")
    with pytest.raises(ValueError, match="certification record"):
        _publish(empty_certification_ledger(), bad_kind)

    missing_id = dict(record)
    del missing_id["certificate_id"]
    with pytest.raises(ValueError, match="certificate_id"):
        _publish(empty_certification_ledger(), missing_id)

    with pytest.raises(ValueError, match="ISO timestamp"):
        _publish(empty_certification_ledger(), record, timestamp_iso="not-a-time")

    with pytest.raises(ValueError, match="source_ref"):
        _publish(empty_certification_ledger(), record, source_ref="")

    malformed_ledger = dict(empty_certification_ledger(), entry_count=1)
    with pytest.raises(ValueError, match="ledger audit failed"):
        _publish(malformed_ledger, record)

    previous = _record(previous_certificate_id="a" * 64)
    with pytest.raises(ValueError, match="genesis"):
        _publish(empty_certification_ledger(), previous)


def test_pointer_only_entry_shape():
    record = _record()
    ledger = _publish(empty_certification_ledger(), record)
    entry = ledger["entries"][0]

    assert entry == {
        "entry_kind": CERTIFICATION_LEDGER_ENTRY_KIND,
        "certificate_id": record["certificate_id"],
        "previous_certificate_id": None,
        "published_at": PUBLISHED_AT,
        "source_ref": LEDGER_SOURCE_REF,
        "certificate_source_ref": SOURCE_REF,
        "previous_entry_digest": None,
        "entry_digest": entry["entry_digest"],
    }
    forbidden = {
        "evidence_basis",
        "report_payload",
        "envelope_payload",
        "raw_metrics",
        "revocation_rows",
        "report_schema_id",
        "report_kind",
    }
    assert forbidden.isdisjoint(entry)


@pytest.mark.parametrize(
    ("mutate", "expected"),
    [
        (
            lambda ledger: ledger["entries"][0].update(
                certificate_id=ledger["entries"][1]["certificate_id"]
            ),
            "duplicate certificate id",
        ),
        (
            lambda ledger: ledger["entries"][0].update(source_ref="reports/changed.json"),
            "entry digest mismatch",
        ),
        (
            lambda ledger: ledger["entries"][1].update(previous_entry_digest="b" * 64),
            "previous_entry_digest mismatch",
        ),
        (
            lambda ledger: ledger["entries"][1].update(previous_certificate_id="c" * 64),
            "certificate-chain discontinuity",
        ),
        (
            lambda ledger: ledger.update(entry_count=7),
            "entry_count mismatch",
        ),
        (
            lambda ledger: ledger.update(head_certificate_id="d" * 64),
            "head_certificate_id mismatch",
        ),
        (
            lambda ledger: ledger.update(head_entry_digest="e" * 64),
            "head_entry_digest mismatch",
        ),
    ],
)
def test_audit_detects_corruptions(mutate, expected):
    first = _record()
    ledger = _publish(empty_certification_ledger(), first)
    second = _record(
        timestamp_iso="2026-06-03T03:04:05+00:00",
        previous_certificate_id=first["certificate_id"],
    )
    ledger = _publish(ledger, second)

    mutate(ledger)

    assert any(expected in error for error in audit_certification_ledger(ledger))


def test_package_all_is_unchanged():
    import bedc_quality_lab

    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert "certification_ledger" not in bedc_quality_lab.__all__
    assert "canonical_digest" not in bedc_quality_lab.__all__
