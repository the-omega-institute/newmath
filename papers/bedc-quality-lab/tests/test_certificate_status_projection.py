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
)
from bedc_quality_lab.certificate_status_projection import (
    project_certificate_standings,
)


CERT_ISSUED_AT = "2026-06-03T01:02:03+00:00"
CERT_PUBLISHED_AT = "2026-06-03T02:03:04+00:00"
CERT_SOURCE_REF = "reports/certificates/run-593.json#certificate"
CERT_LEDGER_SOURCE_REF = "reports/certification-ledger.json"
REVOCATION_PUBLISHED_AT = "2026-06-03T03:04:05+00:00"
REVOCATION_SOURCE_REF = "reports/revocations/run-593.json#revocation"
REVOCATION_LEDGER_SOURCE_REF = "reports/certification-revocation-ledger.json"
UNKNOWN_CERTIFICATE_ID = "f" * 64


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


def test_mixed_active_and_revoked_standings_map_is_exact():
    first = _certificate_record()
    second = _certificate_record(
        model_identity=_model_identity(model_id="bedc-quality-model-secondary"),
        previous_certificate_id=first["certificate_id"],
        source_ref="reports/certificates/run-594.json#certificate",
    )
    cert_ledger = _certification_ledger(first, second)
    revocation = _revocation_record(revoked_certificate_id=second["certificate_id"])
    revocation_ledger = _revocation_ledger(revocation)

    projection = project_certificate_standings(cert_ledger, revocation_ledger)

    assert projection == {
        "standings": {
            first["certificate_id"]: {
                "status": "active",
                "certificate_id": first["certificate_id"],
            },
            second["certificate_id"]: {
                "status": "revoked",
                "certificate_id": second["certificate_id"],
                "revocation_id": revocation["revocation_id"],
                "reason": revocation["reason"],
                "published_at": REVOCATION_PUBLISHED_AT,
                "revocation_source_ref": REVOCATION_LEDGER_SOURCE_REF,
                "certificate_source_ref": revocation["source_ref"],
            },
        },
        "integrity_faults": [],
    }


def test_empty_ledgers_project_empty_envelope():
    cert_ledger = empty_certification_ledger(source_ref=CERT_LEDGER_SOURCE_REF)
    revocation_ledger = empty_certification_revocation_ledger(
        source_ref=REVOCATION_LEDGER_SOURCE_REF,
    )

    projection = project_certificate_standings(cert_ledger, revocation_ledger)

    assert projection == {"standings": {}, "integrity_faults": []}


def test_dangling_revocation_is_integrity_fault_and_not_standing():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    revocation = _revocation_record(
        revoked_certificate_id=UNKNOWN_CERTIFICATE_ID,
        certificate_source_ref="reports/certificates/missing.json#certificate",
    )
    revocation_ledger = _revocation_ledger(revocation)

    projection = project_certificate_standings(cert_ledger, revocation_ledger)

    assert projection == {
        "standings": {
            cert["certificate_id"]: {
                "status": "active",
                "certificate_id": cert["certificate_id"],
            },
        },
        "integrity_faults": [
            {
                "fault": "revocation references unknown certificate_id",
                "certificate_id": UNKNOWN_CERTIFICATE_ID,
                "revocation_id": revocation["revocation_id"],
                "revocation_source_ref": REVOCATION_LEDGER_SOURCE_REF,
                "certificate_source_ref": revocation["source_ref"],
            }
        ],
    }
    assert UNKNOWN_CERTIFICATE_ID not in projection["standings"]


@pytest.mark.parametrize("known_certificate", [True, False])
def test_duplicate_revocation_by_certificate_id_raises(known_certificate):
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    revoked_certificate_id = (
        cert["certificate_id"] if known_certificate else UNKNOWN_CERTIFICATE_ID
    )
    first = _revocation_record(
        revoked_certificate_id=revoked_certificate_id,
        source_ref="reports/revocations/primary.json#revocation",
    )
    second = _revocation_record(
        revoked_certificate_id=revoked_certificate_id,
        previous_revocation_id=first["revocation_id"],
        reason="certificate scope withdrawn",
        source_ref="reports/revocations/secondary.json#revocation",
    )
    revocation_ledger = _revocation_ledger(first, second)

    with pytest.raises(ValueError, match="duplicate revocation for certificate_id"):
        project_certificate_standings(cert_ledger, revocation_ledger)


def test_certification_ledger_audit_error_raises():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    cert_ledger["entry_count"] = True
    revocation_ledger = empty_certification_revocation_ledger(
        source_ref=REVOCATION_LEDGER_SOURCE_REF,
    )

    with pytest.raises(ValueError, match="certification ledger audit failed"):
        project_certificate_standings(cert_ledger, revocation_ledger)


def test_revocation_ledger_audit_error_raises():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    revocation_ledger = empty_certification_revocation_ledger(
        source_ref=REVOCATION_LEDGER_SOURCE_REF,
    )
    revocation_ledger["entry_count"] = True

    with pytest.raises(ValueError, match="revocation ledger audit failed"):
        project_certificate_standings(cert_ledger, revocation_ledger)


def test_projection_envelope_is_pointer_only():
    cert = _certificate_record()
    cert_ledger = _certification_ledger(cert)
    revocation = _revocation_record(
        revoked_certificate_id=UNKNOWN_CERTIFICATE_ID,
        certificate_source_ref="reports/certificates/missing.json#certificate",
    )
    revocation_ledger = _revocation_ledger(revocation)

    projection = project_certificate_standings(cert_ledger, revocation_ledger)

    prohibited_keys = {
        "entry",
        "record",
        "evidence",
        "payload",
        "ledger",
        "report_schema_id",
        "report_kind",
    }
    for status in projection["standings"].values():
        assert not (set(status) & prohibited_keys)
    for fault in projection["integrity_faults"]:
        assert not (set(fault) & prohibited_keys)


def test_package_all_remains_schema_only():
    import bedc_quality_lab

    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
