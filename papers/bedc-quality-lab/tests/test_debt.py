import math

from bedc_quality_lab.debt import assess_debt, format_debt_items


def example_specs():
    return (
        {
            "name": "gaussian-ou-toy-world",
            "sample_count": 384,
            "mixing": "sinusoidal-parabolic-shear",
        },
        {
            "name": "tiny-mlp-2-128-128-2",
            "output_dim": 2,
            "training": "align-cov-mean",
        },
        {
            "name": "fixed-seed-single-source",
            "seed": 23,
            "pair_process": "ornstein-uhlenbeck",
        },
    )


def test_debt_assessment_has_five_bounded_categories():
    source_spec, classifier_spec, stability_spec = example_specs()
    assessment = assess_debt(
        {"approx_identifiability_proxy": 0.8},
        source_spec,
        classifier_spec,
        stability_spec,
    )

    assert [item.kind for item in assessment.items] == [
        "source",
        "distribution",
        "finite-sample",
        "optimization",
        "global-claim",
    ]
    assert all(0.0 <= item.score <= 1.0 for item in assessment.items)
    assert math.isclose(
        assessment.debt_total,
        sum(item.score for item in assessment.items),
        rel_tol=0.0,
        abs_tol=1e-12,
    )


def test_debt_formatter_emits_canonical_keys():
    source_spec, classifier_spec, stability_spec = example_specs()
    assessment = assess_debt({}, source_spec, classifier_spec, stability_spec)

    rows = format_debt_items(assessment)

    assert len(rows) == 5
    for row in rows:
        assert "kind=" in row
        assert "residue=" in row
        assert "severity=" in row
        assert "status=" in row
        assert "score=" in row
