import pytest

from bedc_quality_lab.canonical_digest import canonical_json_digest
from bedc_quality_lab.certification import issue_certification_record
from bedc_quality_lab.certification_ledger import (
    empty_certification_ledger,
    publish_certification_record,
)
from bedc_quality_lab.certification_revocation import (
    CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND,
    CERTIFICATION_REVOCATION_LEDGER_KIND,
    empty_certification_revocation_ledger,
    issue_certification_revocation_record,
    publish_certification_revocation,
)
from bedc_quality_lab.certificate_status import resolve_certificate_status


CERT_ISSUED_AT = "2026-06-03T01:02:03+00:00"
CERT_PUBLISHED_AT = "2026-06-03T02:03:04+00:00"
CERT_SOURCE_REF = "reports/certificates/run-588.json#certificate"
CERT_LEDGER_SOURCE_REF = "reports/certification-ledger.json"
REVOCATION_PUBLISHED_AT = "2026-06-03T03:04:05+00:00"
REVOCATION_SOURCE_REF = "reports/revocations/run-588.json#revocation"
REVOCATION_LEDGER_SOURCE_REF = "reports/certification-revocation-ledger.json"


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
            "scorecard_ready": True,
        },
    }
    base.update(overrides)
    return base


def _certificate_record(**overrides):
    return issue_certification_record(
        overrides.pop("model_identity", _model_identity()),
        overrides.pop("verdict_decision", _verdict_decision()),
        timestamp_iso=overrides.pop("timestamp_iso", CERT_ISSUED_AT),
        source_ref=overrides.pop("source_ref", CERT_SOURCE_REF),
        previous_certificate_id=overrides.pop("previous_certificate_id", None),
    )


def _certification_ledger(*records):
    ledger = empty_certification_ledger(source_ref=CERT_LEDGER_SOURCE_REF)
    for record in records:
        ledger = publish_certification_record(
            ledger,
            record,
            timestamp_iso=CERT_PUBLISHED_AT,
            source_ref=CERT_LEDGER_SOURCE_REF,
        )
    return ledger


def _revocation_record(**overrides):
    return issue_certification_revocation_record(
        revoked_certificate_id=overrides.pop("revoked_certificate_id"),
        previous_revocation_id=overrides.pop("previous_revocation_id", None),
        reason=overrides.pop("reason", "certificate scope no longer holds"),
        source_ref=overrides.pop("source_ref", REVOCATION_SOURCE_REF),
        certificate_source_ref=overrides.pop(
            "certificate_source_ref",
            CERT_SOURCE_REF,
        ),
    )


def _revocation_entry(
    revocation_record,
    *,
    published_at=REVOCATION_PUBLISHED_AT,
    source_ref=REVOCATION_LEDGER_SOURCE_REF,
    previous_entry_digest=None,
):
    entry_basis = {
        "entry_kind": CERTIFICATION_REVOCATION_LEDGER_ENTRY_KIND,
        "revocation_id": revocation_record["revocation_id"],
        "revoked_certificate_id": revocation_record["revoked_certificate_id"],
        "previous_revocation_id": revocation_record["previous_revocation_id"],
        "reason": revocation_record["reason"],
        "published_at": published_at,
        "source_ref": source_ref,
        "certificate_source_ref": revocation_record["source_ref"],
        "previous_entry_digest": previous_entry_digest,
    }
    return {
        **entry_basis,
        "entry_digest": canonical_json_digest(entry_basis),
    }


def _revocation_ledger(*records):
    entries = []
    previous_entry_digest = None
    for record in records:
        entry = _revocation_entry(
            record,
            previous_entry_digest=previous_entry_digest,
        )
        entries.append(entry)
        previous_entry_digest = entry["entry_digest"]
    head = entries[-1] if entries else None
    return {
        "ledger_kind": CERTIFICATION_REVOCATION_LEDGER_KIND,
        "source_ref": REVOCATION_LEDGER_SOURCE_REF,
        "entries": entries,
        "head_revocation_id": None if head is None else head["revocation_id"],
        "head_entry_digest": None if head is None else head["entry_digest"],
        "entry_count": len(entries),
    }


def test_revoked_status_has_exact_pointer_shape():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    revocation = _revocation_record(revoked_certificate_id=cert["certificate_id"])
    revocation_ledger = _revocation_ledger(revocation)

    status = resolve_certificate_status(
        cert_ledger,
        revocation_ledger,
        cert["certificate_id"],
    )

    assert status == {
        "status": "revoked",
        "certificate_id": cert["certificate_id"],
        "revocation_id": revocation["revocation_id"],
        "reason": revocation["reason"],
        "published_at": REVOCATION_PUBLISHED_AT,
        "revocation_source_ref": REVOCATION_LEDGER_SOURCE_REF,
        "certificate_source_ref": revocation["source_ref"],
    }
    assert set(status) == {
        "status",
        "certificate_id",
        "revocation_id",
        "reason",
        "published_at",
        "revocation_source_ref",
        "certificate_source_ref",
    }
    assert not (
        set(status)
        & {
            "entry",
            "record",
            "evidence",
            "payload",
            "metric",
            "ledger",
            "digest-basis",
            "report_schema_id",
            "report_kind",
        }
    )


def test_dangling_matching_revocation_raises_after_audits_pass():
    known_cert = _certificate_record()
    cert_ledger = _certification_ledger(known_cert)
    missing_certificate_id = "f" * 64
    revocation = _revocation_record(revoked_certificate_id=missing_certificate_id)
    revocation_ledger = _revocation_ledger(revocation)

    with pytest.raises(ValueError, match="revocation references unknown certificate_id"):
        resolve_certificate_status(
            cert_ledger,
            revocation_ledger,
            missing_certificate_id,
        )


def test_active_and_unknown_status_shapes_are_minimal():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    revocation_ledger = empty_certification_revocation_ledger(
        source_ref=REVOCATION_LEDGER_SOURCE_REF,
    )

    assert resolve_certificate_status(
        cert_ledger,
        revocation_ledger,
        cert["certificate_id"],
    ) == {"status": "active", "certificate_id": cert["certificate_id"]}
    assert resolve_certificate_status(
        cert_ledger,
        revocation_ledger,
        "0" * 64,
    ) == {"status": "unknown", "certificate_id": "0" * 64}


def test_certification_audit_errors_fail_closed():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    cert_ledger["entry_count"] = True
    revocation_ledger = empty_certification_revocation_ledger()

    with pytest.raises(ValueError, match="certification ledger audit failed"):
        resolve_certificate_status(
            cert_ledger,
            revocation_ledger,
            cert["certificate_id"],
        )


def test_revocation_audit_errors_fail_closed():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    revocation_ledger = empty_certification_revocation_ledger()
    revocation_ledger["entry_count"] = True

    with pytest.raises(ValueError, match="revocation ledger audit failed"):
        resolve_certificate_status(
            cert_ledger,
            revocation_ledger,
            cert["certificate_id"],
        )


def test_duplicate_matching_revocation_raises():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    first = _revocation_record(revoked_certificate_id=cert["certificate_id"])
    second = _revocation_record(
        revoked_certificate_id=cert["certificate_id"],
        previous_revocation_id=first["revocation_id"],
        reason="certificate scope withdrawn",
        source_ref="reports/revocations/run-589.json#revocation",
    )
    revocation_ledger = _revocation_ledger(first, second)

    with pytest.raises(ValueError, match="duplicate revocation for certificate_id"):
        resolve_certificate_status(
            cert_ledger,
            revocation_ledger,
            cert["certificate_id"],
        )


@pytest.mark.parametrize("certificate_id", ["", None, 7, True])
def test_certificate_id_must_be_non_empty_string(certificate_id):
    with pytest.raises(ValueError, match="certificate_id must be a non-empty string"):
        resolve_certificate_status(
            empty_certification_ledger(),
            empty_certification_revocation_ledger(),
            certificate_id,
        )


def test_package_all_stays_at_envelope_only():
    import bedc_quality_lab

    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert "certificate_status" not in bedc_quality_lab.__all__


def test_revocation_publish_path_can_feed_status_resolution():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    first = _revocation_record(revoked_certificate_id="1" * 64)
    ledger = _revocation_ledger(first)
    second = _revocation_record(
        revoked_certificate_id=cert["certificate_id"],
        previous_revocation_id=first["revocation_id"],
        source_ref="reports/revocations/run-590.json#revocation",
    )
    revocation_ledger = publish_certification_revocation(
        ledger,
        second,
        timestamp_iso="2026-06-03T04:05:06+00:00",
        source_ref="reports/certification-revocation-ledger-page.json",
    )

    status = resolve_certificate_status(
        cert_ledger,
        revocation_ledger,
        cert["certificate_id"],
    )

    assert status["status"] == "revoked"
    assert status["revocation_source_ref"] == (
        "reports/certification-revocation-ledger-page.json"
    )
