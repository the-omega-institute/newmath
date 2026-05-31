from bedc_quality_lab.debt import assess_debt
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps


def test_ledger_gaps_derive_from_debt_and_specs():
    source_spec = {
        "name": "gaussian-ou-toy-world",
        "sample_count": 384,
        "mixing": "sinusoidal-parabolic-shear",
    }
    classifier_spec = {
        "name": "tiny-mlp-2-128-128-2",
        "output_dim": 2,
        "training": "align-cov-mean",
    }
    stability_spec = {
        "name": "fixed-seed-single-source",
        "seed": 23,
        "pair_process": "ornstein-uhlenbeck",
    }
    metrics = {"approx_identifiability_proxy": 0.8}
    assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec)

    gaps = derive_ledger_gaps(metrics, source_spec, classifier_spec, stability_spec, assessment)
    rows = format_ledger_gaps(gaps)

    assert rows
    assert all(row.startswith("kind=") for row in rows)
    assert all("; residue=" in row for row in rows)
    assert all("; severity=" in row for row in rows)
    assert all("; status=" in row for row in rows)
    assert any(
        gap.kind == "source" and gap.residue == "source-coverage" and gap.status in {"open", "partial"}
        for gap in gaps
    )
    assert any(
        gap.kind == "source"
        and gap.residue == "mixing-family-coverage"
        and gap.status in {"open", "partial"}
        for gap in gaps
    )
    assert any(
        gap.kind == "generalization"
        and gap.residue == "global-claim-boundary"
        and gap.status in {"open", "partial"}
        for gap in gaps
    )


def test_ledger_metric_gap_pins_partial_and_open_statuses_below_margin():
    source_spec = {"source_count": 3, "sample_count": 2048, "mixing": ["a", "b", "c"]}
    classifier_spec = {"name": "certified-classifier", "training": "certified"}
    stability_spec = {"multi_seed": True}
    assessment = assess_debt(
        {"approx_identifiability_proxy": 0.8},
        {**source_spec, "global_claim": True},
        classifier_spec,
        stability_spec,
    )

    partial_gaps = derive_ledger_gaps(
        {"approx_identifiability_proxy": 0.5},
        source_spec,
        classifier_spec,
        stability_spec,
        assessment,
    )
    open_gaps = derive_ledger_gaps(
        {"approx_identifiability_proxy": 0.49},
        source_spec,
        classifier_spec,
        stability_spec,
        assessment,
    )

    assert partial_gaps == [
        type(partial_gaps[0])(
            kind="verification",
            residue="identifiability-proxy-margin",
            severity="medium",
            status="partial",
        )
    ]
    assert open_gaps == [
        type(open_gaps[0])(
            kind="verification",
            residue="identifiability-proxy-margin",
            severity="high",
            status="open",
        )
    ]


def test_ledger_filters_closed_debt_items():
    source_spec = {
        "source_count": 3,
        "sample_count": 2048,
        "mixing": ["sinusoidal", "parabolic", "shear"],
        "global_claim": True,
    }
    classifier_spec = {"name": "certified-classifier", "training": "certified"}
    stability_spec = {"multi_seed": True}
    metrics = {"approx_identifiability_proxy": 0.8}
    assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec)

    assert {item.status for item in assessment.items} == {"closed"}
    assert derive_ledger_gaps(metrics, source_spec, classifier_spec, stability_spec, assessment) == []
