from dataclasses import replace

from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.tensor_namecert_candidate import (
    closure_status_rows,
    from_quality_evidence_envelope,
)


def make_envelope(**overrides):
    data = {
        "schema_id": SCHEMA_ID,
        "run_id": "closure-test",
        "source_spec": {"name": "source"},
        "pattern_spec": {"name": "pattern", "status": "sufficient"},
        "classifier_spec": {"name": "classifier", "status": "closed"},
        "stability_spec": {"name": "stability", "critical_gaps": ["unbounded drift"]},
        "metrics": {"quality_q": 0.5},
        "ledger_gaps": [],
        "debt_items": [],
        "artifacts": {"report": "reports/quality_report.md"},
        "bedc_refs": [],
    }
    data.update(overrides)
    return QualityEvidenceEnvelope(**data)


def row_map(candidate):
    return {field: (level, provenance) for field, level, provenance in closure_status_rows(candidate)}


def test_name_only_spec_is_present_not_closed():
    candidate = from_quality_evidence_envelope(make_envelope())

    assert candidate.closure_status["source_spec"] == "present"
    assert row_map(candidate)["source_spec"] == ("present", "name_only")


def test_closed_spec_requires_explicit_sufficient_or_closed_status():
    candidate = from_quality_evidence_envelope(
        make_envelope(
            source_spec={"name": "source", "status": "sufficient"},
            pattern_spec={"name": "pattern", "status": "closed"},
            classifier_spec={"name": "classifier", "status": "verified"},
        )
    )

    assert candidate.closure_status["source_spec"] == "closed"
    assert candidate.closure_status["pattern_spec"] == "closed"
    assert candidate.closure_status["classifier_spec"] == "partial"
    assert row_map(candidate)["classifier_spec"] == ("partial", "explicit_status")


def test_critical_gaps_force_partial():
    candidate = from_quality_evidence_envelope(
        make_envelope(source_spec={"name": "source", "status": "closed", "critical_gaps": ["gap"]})
    )

    assert candidate.closure_status["source_spec"] == "partial"
    assert row_map(candidate)["source_spec"] == ("partial", "critical_gaps")


def test_missing_spec_is_missing():
    candidate = from_quality_evidence_envelope(make_envelope(source_spec={}))

    assert candidate.closure_status["source_spec"] == "missing"
    assert row_map(candidate)["source_spec"] == ("missing", "missing_name")


def test_ledger_open_gaps_force_partial():
    candidate = from_quality_evidence_envelope(
        make_envelope(
            ledger_gaps=["kind=source; residue=coverage; severity=high; status=open"],
            debt_items=["kind=source; residue=coverage; severity=high; status=closed; score=0.0"],
        )
    )

    assert candidate.closure_status["ledger_policy"] == "partial"
    assert row_map(candidate)["ledger_policy"] == ("partial", "open_ledger_rows")


def test_closed_ledger_requires_all_rows_explicitly_closed():
    candidate = from_quality_evidence_envelope(
        make_envelope(
            ledger_gaps=["kind=source; residue=coverage; severity=none; status=closed"],
            debt_items=["kind=verification; residue=bound; severity=none; status=sufficient; score=0.0"],
        )
    )

    assert candidate.closure_status["ledger_policy"] == "closed"
    assert row_map(candidate)["ledger_policy"] == ("closed", "explicit_closed_ledger_rows")


def test_missing_ledger_policy_mapping_is_missing():
    candidate = from_quality_evidence_envelope(make_envelope())
    patched = replace(candidate, ledger_policy={"artifacts": {}})

    assert row_map(patched)["ledger_policy"] == ("missing", "missing_ledger_policy")


def test_scope_seal_without_not_claimed_is_partial():
    candidate = from_quality_evidence_envelope(make_envelope())
    patched = replace(candidate, scope_seal={**candidate.scope_seal, "not_claimed": []})

    assert row_map(patched)["scope_seal"] == ("partial", "missing_not_claimed")
