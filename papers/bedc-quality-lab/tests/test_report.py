from bedc_quality_lab.report import render_quality_report
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope


def test_report_projection_uses_envelope_values():
    envelope = QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id="projection-test",
        source_spec={"name": "source-from-envelope"},
        pattern_spec={"name": "pattern-from-envelope"},
        classifier_spec={"name": "classifier-from-envelope"},
        stability_spec={"name": "stability-from-envelope"},
        metrics={
            "linear_identifiability_r2": 0.1234567,
            "approx_identifiability_proxy": 0.2222222,
        },
        ledger_gaps=["gap-from-envelope"],
        debt_items=["debt-from-envelope"],
        artifacts={"envelope": "reports/example_envelope.json"},
        bedc_refs=["papers/bedc/preamble.tex:closurestatus"],
    )

    report = render_quality_report(envelope)
    assert "projection-test" in report
    assert "source-from-envelope" in report
    assert "0.123457" in report
    assert "gap-from-envelope" in report
    assert "debt-from-envelope" in report
    assert "reports/example_envelope.json" in report
