import pytest

from bedc_quality_lab.certification import (
    CERTIFICATION_RECORD_KIND,
    issue_certification_record,
)


ISSUED_AT = "2026-06-03T01:02:03+00:00"
DECIDED_AT = "2026-06-03T00:00:00+00:00"
SOURCE_REF = "reports/verdicts/run-57.json#terminal"


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
        "decided_at": DECIDED_AT,
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


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def test_identical_inputs_return_identical_certificate_id_and_record():
    first = _record()
    second = _record()

    assert first == second
    assert first["certificate_id"] == second["certificate_id"]


def test_certificate_id_changes_when_identity_verdict_basis_or_pointers_change():
    base = _record()
    changed_records = [
        _record(source_ref="reports/verdicts/other.json#terminal"),
        _record(timestamp_iso="2026-06-03T02:03:04+00:00"),
        _record(model_identity=_model_identity(model_version="quality-2026-06-04")),
        _record(verdict_decision=_verdict_decision(reason="audit-not-consistent")),
        _record(
            verdict_decision=_verdict_decision(
                evidence_basis={
                    "audit_status": "consistent",
                    "record_roles": ["before", "after", "control"],
                    "scorecard_ready": True,
                    "nested": {"quality_q_ci95_low": 0.5},
                }
            )
        ),
        _record(previous_certificate_id="8" * 64),
    ]

    assert all(
        changed["certificate_id"] != base["certificate_id"]
        for changed in changed_records
    )


def test_issued_at_and_decided_at_preserve_caller_and_verdict_timestamps():
    record = _record()

    assert record["issued_at"] == ISSUED_AT
    assert record["decided_at"] == DECIDED_AT


def test_record_kind_is_certification_record_literal():
    assert _record()["record_kind"] == CERTIFICATION_RECORD_KIND
    assert _record()["record_kind"] == "certification-record"


def test_previous_certificate_id_is_present_without_previous_certificate_ref():
    record = _record(previous_certificate_id="a" * 64)

    assert record["previous_certificate_id"] == "a" * 64
    assert "previous_certificate_ref" not in record


def test_record_is_pointer_only_and_contains_evidence_basis_digest_only():
    record = _record()
    keys = set(_walk_keys(record))

    assert "evidence_basis_digest" in record
    assert "evidence_basis" not in keys
    assert "report_payload" not in keys
    assert "envelope_payload" not in keys
    assert "report_schema_id" not in keys
    assert "report_kind" not in keys


def test_certifies_model_quality_is_not_emitted():
    assert "certifies_model_quality" not in set(_walk_keys(_record()))


def test_issue_function_imports_from_module_but_not_package_all():
    import bedc_quality_lab
    from bedc_quality_lab.certification import issue_certification_record as imported

    assert imported is issue_certification_record
    assert "certification" not in bedc_quality_lab.__all__
    assert "issue_certification_record" not in bedc_quality_lab.__all__


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("timestamp_iso", "", "timestamp_iso must be a non-empty string"),
        ("source_ref", "", "source_ref must be a non-empty string"),
        (
            "previous_certificate_id",
            "",
            "previous_certificate_id must be a non-empty string or None",
        ),
        (
            "previous_certificate_id",
            7,
            "previous_certificate_id must be a non-empty string or None",
        ),
    ],
)
def test_public_string_inputs_raise_for_bad_values(field, value, message):
    kwargs = {
        "timestamp_iso": ISSUED_AT,
        "source_ref": SOURCE_REF,
        "previous_certificate_id": None,
        field: value,
    }

    with pytest.raises(ValueError, match=message):
        issue_certification_record(
            _model_identity(),
            _verdict_decision(),
            **kwargs,
        )


def test_verdict_raises_for_unsupported_value():
    with pytest.raises(ValueError, match="verdict must be one of"):
        _record(verdict_decision=_verdict_decision(verdict="maybe"))


def test_evidence_basis_raises_for_non_mapping_value():
    with pytest.raises(TypeError, match="evidence_basis must be a mapping"):
        _record(verdict_decision=_verdict_decision(evidence_basis=[]))


def test_evidence_basis_raises_for_absent_key():
    verdict_decision = _verdict_decision()
    del verdict_decision["evidence_basis"]

    with pytest.raises(KeyError, match="evidence_basis"):
        _record(verdict_decision=verdict_decision)


@pytest.mark.parametrize(
    ("value", "exception_type", "message"),
    [
        (None, KeyError, "model_id"),
        ("", ValueError, "model_id must be a non-empty string"),
        (7, ValueError, "model_id must be a non-empty string"),
    ],
)
def test_model_id_raises_for_absent_or_bad_values(
    value,
    exception_type,
    message,
):
    model_identity = _model_identity()
    if value is None:
        del model_identity["model_id"]
    else:
        model_identity["model_id"] = value

    with pytest.raises(exception_type, match=message):
        _record(model_identity=model_identity)


@pytest.mark.parametrize(
    ("field", "value", "exception_type", "message"),
    [
        ("verdict", None, KeyError, "verdict"),
        ("verdict", "", ValueError, "verdict must be a non-empty string"),
        ("verdict", 7, ValueError, "verdict must be a non-empty string"),
        ("reason", None, KeyError, "reason"),
        ("reason", "", ValueError, "reason must be a non-empty string"),
        ("reason", 7, ValueError, "reason must be a non-empty string"),
        ("decided_at", None, KeyError, "decided_at"),
        ("decided_at", "", ValueError, "decided_at must be a non-empty string"),
        ("decided_at", 7, ValueError, "decided_at must be a non-empty string"),
    ],
)
def test_verdict_decision_string_fields_raise_for_absent_or_bad_values(
    field,
    value,
    exception_type,
    message,
):
    verdict_decision = _verdict_decision()
    if value is None:
        del verdict_decision[field]
    else:
        verdict_decision[field] = value

    with pytest.raises(exception_type, match=message):
        _record(verdict_decision=verdict_decision)


@pytest.mark.parametrize("field", ["model_version", "classifier_id", "scope_id"])
@pytest.mark.parametrize("value", ["", 7])
def test_optional_identity_fields_raise_for_bad_values(field, value):
    with pytest.raises(
        ValueError,
        match=f"{field} must be a non-empty string or None",
    ):
        _record(model_identity=_model_identity(**{field: value}))


def test_optional_identity_fields_accept_none():
    record = _record(
        model_identity=_model_identity(
            model_version=None,
            classifier_id=None,
            scope_id=None,
        )
    )

    assert record["model_version"] is None
    assert record["classifier_id"] is None
    assert record["scope_id"] is None
