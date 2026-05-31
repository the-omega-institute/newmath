import pytest

from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope


def envelope_kwargs():
    return {
        "schema_id": SCHEMA_ID,
        "run_id": "schema-test",
        "source_spec": {"name": "source"},
        "pattern_spec": {"name": "pattern"},
        "classifier_spec": {"name": "classifier"},
        "stability_spec": {"name": "stability"},
        "metrics": {"linear_identifiability_r2": 0.75},
        "ledger_gaps": ["finite-sample-only"],
        "debt_items": ["distribution-debt"],
        "artifacts": {"report": "reports/quality_report.md"},
        "bedc_refs": ["papers/bedc/preamble.tex:closurestatus"],
    }


def test_schema_requires_evidence_boundary():
    envelope = QualityEvidenceEnvelope(**envelope_kwargs())
    assert envelope.schema_id == SCHEMA_ID
    data = envelope.to_dict()
    assert set(data) == {
        "schema_id",
        "run_id",
        "source_spec",
        "pattern_spec",
        "classifier_spec",
        "stability_spec",
        "metrics",
        "ledger_gaps",
        "debt_items",
        "artifacts",
        "bedc_refs",
    }

    bad = envelope_kwargs()
    bad["schema_id"] = "bedc-quality-lab:namecert"
    with pytest.raises(ValueError, match="schema_id"):
        QualityEvidenceEnvelope(**bad)


def test_schema_rejects_bedc_rule_copies():
    bad = envelope_kwargs()
    bad["bedc_refs"] = [
        "closurestatus records theoryclosure and formalstatus and must use BEDC rule prose"
    ]
    with pytest.raises(ValueError, match="opaque pointers"):
        QualityEvidenceEnvelope(**bad)

    good = envelope_kwargs()
    good["bedc_refs"] = ["papers/bedc/preamble.tex:closurestatus"]
    assert QualityEvidenceEnvelope(**good).bedc_refs == good["bedc_refs"]
