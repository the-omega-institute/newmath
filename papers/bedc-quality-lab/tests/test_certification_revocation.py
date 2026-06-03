import pytest

from bedc_quality_lab.canonical_digest import canonical_json_digest
from bedc_quality_lab.certification_revocation import (
    CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND,
    CERTIFICATION_REVOCATION_LEDGER_KIND,
    audit_certification_revocation_ledger,
    empty_certification_revocation_ledger,
    issue_certification_revocation_record,
    publish_certification_revocation,
)


PUBLISHED_AT = "2026-06-03T02:03:04+00:00"
SOURCE_REF = "reports/revocations/run-57.json#revocation"
LEDGER_SOURCE_REF = "reports/certification-revocation-ledger.json"
CERTIFICATE_SOURCE_REF = "reports/certificates/run-57.json#certificate"
CERTIFICATE_ID = "a" * 64
SECOND_CERTIFICATE_ID = "b" * 64


def _record(**overrides):
    return issue_certification_revocation_record(
        revoked_certificate_id=overrides.pop(
            "revoked_certificate_id",
            CERTIFICATE_ID,
        ),
        previous_revocation_id=overrides.pop("previous_revocation_id", None),
        reason=overrides.pop("reason", "certificate scope no longer holds"),
        source_ref=overrides.pop("source_ref", SOURCE_REF),
        certificate_source_ref=overrides.pop(
            "certificate_source_ref",
            CERTIFICATE_SOURCE_REF,
        ),
    )


def _publish(ledger, record, **overrides):
    return publish_certification_revocation(
        ledger,
        record,
        timestamp_iso=overrides.pop("timestamp_iso", PUBLISHED_AT),
        source_ref=overrides.pop("source_ref", LEDGER_SOURCE_REF),
    )


def _entry_from_record(record, *, published_at=PUBLISHED_AT, previous_entry_digest=None):
    entry_basis = {
        "entry_kind": CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND,
        "revocation_id": record["revocation_id"],
        "revoked_certificate_id": record["revoked_certificate_id"],
        "previous_revocation_id": record["previous_revocation_id"],
        "reason": record["reason"],
        "published_at": published_at,
        "source_ref": LEDGER_SOURCE_REF,
        "certificate_source_ref": record["certificate_source_ref"],
        "previous_entry_digest": previous_entry_digest,
    }
    return {
        **entry_basis,
        "entry_digest": canonical_json_digest(entry_basis),
    }


def _ledger_with_entries(*records):
    entries = []
    previous_entry_digest = None
    for record in records:
        entry = _entry_from_record(
            record,
            previous_entry_digest=previous_entry_digest,
        )
        entries.append(entry)
        previous_entry_digest = entry["entry_digest"]
    head = entries[-1] if entries else None
    return {
        "ledger_kind": CERTIFICATION_REVOCATION_LEDGER_KIND,
        "source_ref": None,
        "entries": entries,
        "head_revocation_id": None if head is None else head["revocation_id"],
        "head_entry_digest": None if head is None else head["entry_digest"],
        "entry_count": len(entries),
    }


def _two_entry_ledger():
    first = _record()
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
        source_ref="reports/revocations/run-58.json#revocation",
    )
    return _ledger_with_entries(first, second)


def _with_revocation_digest(record):
    basis = dict(record)
    basis.pop("revocation_id", None)
    return {
        "revocation_id": canonical_json_digest(basis),
        **basis,
    }


def _audit_errors_after(mutate, *, entries=1):
    if entries == 0:
        ledger = empty_certification_revocation_ledger()
    elif entries == 1:
        ledger = _ledger_with_entries(_record())
    else:
        ledger = _two_entry_ledger()
    mutate(ledger)
    return audit_certification_revocation_ledger(ledger)


def test_empty_ledger_and_genesis_entry_shape():
    ledger = empty_certification_revocation_ledger(source_ref=LEDGER_SOURCE_REF)
    record = _record()
    seeded = _ledger_with_entries(record)

    assert ledger == {
        "ledger_kind": CERTIFICATION_REVOCATION_LEDGER_KIND,
        "source_ref": LEDGER_SOURCE_REF,
        "entries": [],
        "head_revocation_id": None,
        "head_entry_digest": None,
        "entry_count": 0,
    }
    assert seeded["ledger_kind"] == CERTIFICATION_REVOCATION_LEDGER_KIND
    assert seeded["entry_count"] == 1
    assert seeded["head_revocation_id"] == record["revocation_id"]
    assert seeded["head_entry_digest"] == seeded["entries"][0]["entry_digest"]
    assert audit_certification_revocation_ledger(seeded) == []


def test_linked_append_updates_head_and_back_pointers():
    first = _record()
    ledger = _ledger_with_entries(first)
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
        source_ref="reports/revocations/run-58.json#revocation",
    )

    published = _publish(ledger, second, timestamp_iso="2026-06-03T04:05:06+00:00")

    first_entry, second_entry = published["entries"]
    assert published["entry_count"] == 2
    assert published["head_revocation_id"] == second["revocation_id"]
    assert first_entry["previous_revocation_id"] is None
    assert second_entry["previous_revocation_id"] == first["revocation_id"]
    assert second_entry["previous_entry_digest"] == first_entry["entry_digest"]
    assert audit_certification_revocation_ledger(published) == []


def test_publish_returns_immutable_copy_and_does_not_mutate_input():
    record = _record()
    ledger = _ledger_with_entries(record)
    before = {
        **ledger,
        "entries": [dict(entry) for entry in ledger["entries"]],
    }

    copy = _publish(ledger, record)

    assert copy == ledger
    assert copy is not ledger
    assert copy["entries"] is not ledger["entries"]
    assert copy["entries"][0] is not ledger["entries"][0]
    copy["entries"][0]["source_ref"] = "reports/changed.json"
    assert ledger == before


def test_current_head_publish_is_idempotent():
    record = _record()
    ledger = _ledger_with_entries(record)

    again = _publish(ledger, record)

    assert again == ledger
    assert len(again["entries"]) == 1


def test_publish_rejects_empty_ledger():
    with pytest.raises(ValueError, match="empty revocation ledger"):
        _publish(empty_certification_revocation_ledger(), _record())


def test_stale_duplicate_and_fork_rejection():
    first = _record()
    ledger = _ledger_with_entries(first)
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
        source_ref="reports/revocations/run-58.json#revocation",
    )
    ledger = _publish(ledger, second)
    sibling = _record(
        revoked_certificate_id="c" * 64,
        source_ref="reports/revocations/sibling.json#revocation",
        previous_revocation_id=first["revocation_id"],
    )

    with pytest.raises(ValueError, match="already appears"):
        _publish(ledger, first)
    with pytest.raises(ValueError, match="discontinuity"):
        _publish(ledger, sibling)


def test_tampered_revocation_record_is_rejected():
    first = _record()
    ledger = _ledger_with_entries(first)
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
    )
    tampered = dict(second)
    tampered["reason"] = "tampered"

    with pytest.raises(ValueError, match="revocation_id mismatch"):
        _publish(ledger, tampered)


def test_publish_rejects_missing_revoked_certificate_id():
    first = _record()
    ledger = _ledger_with_entries(first)
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
    )
    missing_id = dict(second)
    del missing_id["revoked_certificate_id"]
    missing_id = _with_revocation_digest(missing_id)

    with pytest.raises(ValueError, match="revoked_certificate_id"):
        _publish(ledger, missing_id)


def test_publish_rejects_malformed_ids_timestamp_source_and_ledger():
    first = _record()
    ledger = _ledger_with_entries(first)
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
    )

    missing_id = dict(second)
    del missing_id["revocation_id"]
    with pytest.raises(ValueError, match="revocation_id"):
        _publish(ledger, missing_id)

    with pytest.raises(ValueError, match="ISO timestamp"):
        _publish(ledger, second, timestamp_iso="not-a-time")

    with pytest.raises(ValueError, match="source_ref"):
        _publish(ledger, second, source_ref="")

    malformed_ledger = dict(ledger, entry_count=True)
    with pytest.raises(ValueError, match="ledger audit failed"):
        _publish(malformed_ledger, second)

    malformed_previous = _with_revocation_digest(
        dict(second, previous_revocation_id=True)
    )
    with pytest.raises(
        ValueError,
        match="previous_revocation_id must be a non-empty string or None",
    ):
        _publish(ledger, malformed_previous)


@pytest.mark.parametrize("source_ref", ["", 3, True])
def test_empty_ledger_rejects_malformed_source_ref(source_ref):
    with pytest.raises(ValueError, match="source_ref must be a non-empty string or None"):
        empty_certification_revocation_ledger(source_ref=source_ref)


@pytest.mark.parametrize(
    ("field", "value", "match"),
    [
        ("reason", "", "reason"),
        ("source_ref", "", "record source_ref"),
        ("certificate_source_ref", True, "certificate_source_ref"),
    ],
)
def test_publish_rejects_malformed_record_strings(field, value, match):
    first = _record()
    ledger = _ledger_with_entries(first)
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
    )
    malformed = _with_revocation_digest(dict(second, **{field: value}))

    with pytest.raises(ValueError, match=match):
        _publish(ledger, malformed)


def test_pointer_only_entry_shape():
    record = _record()
    ledger = _ledger_with_entries(record)
    entry = ledger["entries"][0]

    assert entry == {
        "entry_kind": CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND,
        "revocation_id": record["revocation_id"],
        "revoked_certificate_id": record["revoked_certificate_id"],
        "previous_revocation_id": None,
        "reason": record["reason"],
        "published_at": PUBLISHED_AT,
        "source_ref": LEDGER_SOURCE_REF,
        "certificate_source_ref": CERTIFICATE_SOURCE_REF,
        "previous_entry_digest": None,
        "entry_digest": entry["entry_digest"],
    }
    assert list(entry.keys()) == [
        "entry_kind",
        "revocation_id",
        "revoked_certificate_id",
        "previous_revocation_id",
        "reason",
        "published_at",
        "source_ref",
        "certificate_source_ref",
        "previous_entry_digest",
        "entry_digest",
    ]
    forbidden = {
        "certificate_record",
        "revocation_record",
        "evidence",
        "evidence_basis",
        "payload",
        "metrics",
        "raw_metrics",
        "report_schema_id",
        "report_kind",
    }
    assert forbidden.isdisjoint(entry)


@pytest.mark.parametrize(
    ("mutate", "expected"),
    [
        (
            lambda ledger: ledger["entries"][0].update(
                revocation_id=ledger["entries"][1]["revocation_id"]
            ),
            "duplicate revocation id",
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
            lambda ledger: ledger["entries"][1].update(previous_revocation_id="c" * 64),
            "revocation-chain discontinuity",
        ),
        (
            lambda ledger: ledger.update(entry_count=7),
            "entry_count mismatch",
        ),
        (
            lambda ledger: ledger.update(head_revocation_id="d" * 64),
            "head_revocation_id mismatch",
        ),
        (
            lambda ledger: ledger.update(head_entry_digest="e" * 64),
            "head_entry_digest mismatch",
        ),
        (
            lambda ledger: ledger["entries"][0].pop("revoked_certificate_id"),
            "entry 0 revoked_certificate_id must be a non-empty string",
        ),
    ],
)
def test_audit_detects_corruptions(mutate, expected):
    ledger = _two_entry_ledger()

    mutate(ledger)

    assert any(expected in error for error in audit_certification_revocation_ledger(ledger))


@pytest.mark.parametrize(
    ("entries", "entry_count"),
    [
        (1, True),
        (1, False),
        (1, "1"),
        (1, None),
        (0, True),
        (0, False),
        (0, "0"),
        (0, None),
    ],
)
def test_audit_rejects_non_integer_entry_count(entries, entry_count):
    errors = _audit_errors_after(
        lambda ledger: ledger.update(entry_count=entry_count),
        entries=entries,
    )

    assert "entry_count must be an integer" in errors


def test_publish_rejects_bool_entry_count_before_append():
    first = _record()
    ledger = _ledger_with_entries(first)
    second = _record(
        revoked_certificate_id=SECOND_CERTIFICATE_ID,
        previous_revocation_id=first["revocation_id"],
    )
    ledger = dict(ledger, entry_count=True)

    with pytest.raises(ValueError, match="ledger audit failed"):
        _publish(ledger, second)


@pytest.mark.parametrize(
    ("mutate", "expected", "entries"),
    [
        (
            lambda ledger: ledger.pop("head_entry_digest"),
            "ledger field set mismatch",
            1,
        ),
        (
            lambda ledger: ledger.update(ledger_kind="other"),
            "ledger kind mismatch",
            1,
        ),
        (
            lambda ledger: ledger.update(source_ref=""),
            "ledger source_ref must be a non-empty string or None",
            0,
        ),
        (
            lambda ledger: ledger.update(entries={}),
            "entries must be a list",
            0,
        ),
        (
            lambda ledger: ledger["entries"].__setitem__(0, "not-entry"),
            "entry 0 must be a mapping",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].pop("certificate_source_ref"),
            "entry 0 field set mismatch",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(entry_kind="other"),
            "entry 0 kind mismatch",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(revocation_id=""),
            "entry 0 revocation_id must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(revocation_id=True),
            "entry 0 revocation_id must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][1].update(
                revocation_id=ledger["entries"][0]["revocation_id"]
            ),
            "duplicate revocation id",
            2,
        ),
        (
            lambda ledger: ledger["entries"][0].update(previous_revocation_id=""),
            "entry 0 previous_revocation_id must be a non-empty string or None",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(reason=""),
            "entry 0 reason must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(published_at=""),
            "entry 0 published_at must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(published_at="not-a-time"),
            "entry 0 published_at must be an ISO timestamp",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(source_ref=""),
            "entry 0 source_ref must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(certificate_source_ref=True),
            "entry 0 certificate_source_ref must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].pop("entry_digest"),
            "entry 0 entry_digest must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(entry_digest=""),
            "entry 0 entry_digest must be a non-empty string",
            1,
        ),
        (
            lambda ledger: ledger["entries"][0].update(entry_digest="bad-digest"),
            "entry 0 entry digest mismatch",
            1,
        ),
    ],
)
def test_audit_reports_malformed_ledger_diagnostics(mutate, expected, entries):
    errors = _audit_errors_after(mutate, entries=entries)

    assert any(expected in error for error in errors)


def test_package_all_is_unchanged():
    import bedc_quality_lab

    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert "certification_revocation" not in bedc_quality_lab.__all__
