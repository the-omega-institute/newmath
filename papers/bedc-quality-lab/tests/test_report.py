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
            "quality_benefit": 0.3333333,
            "quality_cost": 0.0444444,
            "quality_debt": 0.1111111,
            "quality_q": 0.1777778,
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
    assert "## Q 投影" in report
    assert "`quality_q`：0.177778" in report
    assert "gap-from-envelope" in report
    assert "debt-from-envelope" in report
    assert "reports/example_envelope.json" in report


def test_report_includes_cost_protocol_section():
    envelope = QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id="protocol-projection-test",
        source_spec={"name": "source-from-envelope"},
        pattern_spec={"name": "pattern-from-envelope"},
        classifier_spec={"name": "classifier-from-envelope"},
        stability_spec={"name": "stability-from-envelope"},
        metrics={
            "quality_benefit": 0.3333333,
            "quality_cost": 0.0444444,
            "quality_debt": 0.1111111,
            "quality_q": 0.1777778,
        },
    )

    report = render_quality_report(envelope)

    assert "## Cost Protocol" in report
    assert "bedc-quality-lab-default-cost-protocol" in report
    assert "`source/source-coverage`: 0.180000" in report
    assert "`source/mixing-family-coverage`: 0.220000" in report
    assert "`source/finite-sample-support`: 0.200000" in report
    assert "`classifier/optimizer-certificate`: 0.200000" in report
    assert "`generalization/global-claim-boundary`: 0.200000" in report
    assert "`quality_q` = `quality_benefit - quality_cost - quality_debt`" in report
    assert "`outside-declared-scope`" in report
    assert "`untested-source-families`" in report
    assert "`unproved-global-generalization`" in report


def test_report_identifiability_bound_section_projects_envelope_metrics_only():
    envelope = QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id="bound-projection-test",
        source_spec={"name": "source-from-envelope"},
        pattern_spec={"name": "pattern-from-envelope"},
        classifier_spec={"name": "classifier-from-envelope"},
        stability_spec={"name": "stability-from-envelope"},
        metrics={
            "linear_identifiability_r2": 0.1234567,
            "alignment_loss": 0.25,
            "theorem3_bound": 0.75,
            "bound_margin": -0.5,
            "quality_q": 0.1777778,
        },
    )

    report = render_quality_report(envelope)

    assert "## Identifiability Bound" in report
    assert "`alignment_loss`：0.250000" in report
    assert "`theorem3_bound`：0.750000" in report
    assert "`bound_margin`：-0.500000" in report
    assert "`actual_recovery_error`" not in report
    assert report.index("## Identifiability Bound") < report.index("## Q 投影")
