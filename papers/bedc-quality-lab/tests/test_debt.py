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


def assert_item(assessment, kind, *, severity, status, score):
    matches = [item for item in assessment.items if item.kind == kind]
    assert len(matches) == 1
    item = matches[0]
    assert item.severity == severity
    assert item.status == status
    assert math.isclose(item.score, score, rel_tol=0.0, abs_tol=1e-12)


def assess_case(source_spec, classifier_spec=None, stability_spec=None):
    return assess_debt(
        {"approx_identifiability_proxy": 0.25},
        source_spec,
        classifier_spec or {"name": "align-classifier", "training": "align-cov-mean"},
        stability_spec or {"name": "single-seed"},
    )


def test_source_coverage_thresholds_pin_closed_partial_open_statuses():
    open_assessment = assess_case({"source_count": 1})
    partial_assessment = assess_case({"source_count": 2})
    closed_assessment = assess_case({"source_count": 3})

    assert_item(open_assessment, "source", severity="high", status="open", score=0.18)
    assert_item(partial_assessment, "source", severity="medium", status="partial", score=0.09)
    assert_item(closed_assessment, "source", severity="none", status="closed", score=0.0)


def test_distribution_coverage_thresholds_pin_closed_partial_open_statuses():
    open_assessment = assess_case({"mixing": "single-family"})
    partial_assessment = assess_case({"mixing": ["a", "b"]})
    closed_assessment = assess_case({"mixing": ["a", "b", "c"]})

    assert_item(open_assessment, "distribution", severity="high", status="open", score=0.22)
    assert_item(partial_assessment, "distribution", severity="medium", status="partial", score=0.11)
    assert_item(closed_assessment, "distribution", severity="none", status="closed", score=0.0)


def test_finite_sample_thresholds_pin_all_score_bands():
    below_support = assess_case({"sample_count": 511})
    weak_support = assess_case({"sample_count": 512})
    partial_support = assess_case({"sample_count": 1024})
    closed_support = assess_case({"sample_count": 2048})

    assert_item(below_support, "finite-sample", severity="high", status="open", score=0.20)
    assert_item(weak_support, "finite-sample", severity="medium", status="partial", score=0.10)
    assert_item(partial_support, "finite-sample", severity="low", status="partial", score=0.05)
    assert_item(closed_support, "finite-sample", severity="none", status="closed", score=0.0)


def test_optimization_certified_deterministic_and_open_training_statuses():
    open_assessment = assess_case({}, {"name": "tiny-mlp", "training": "align-cov-mean"})
    partial_assessment = assess_case(
        {},
        {"name": "standardized-observation", "training": "deterministic-standardization"},
    )
    certified_assessment = assess_case({}, {"name": "certified-search", "training": "align"})
    exhaustive_assessment = assess_case({}, {"name": "finite", "training": "exhaustive-grid"})

    assert_item(open_assessment, "optimization", severity="high", status="open", score=0.20)
    assert_item(partial_assessment, "optimization", severity="medium", status="partial", score=0.10)
    assert_item(certified_assessment, "optimization", severity="none", status="closed", score=0.0)
    assert_item(exhaustive_assessment, "optimization", severity="none", status="closed", score=0.0)


def test_global_claim_multi_seed_thresholds_pin_closed_partial_open_statuses():
    open_assessment = assess_case({"global_claim": False}, stability_spec={"multi_seed": True})
    partial_assessment = assess_case({"global_claim": True}, stability_spec={"multi_seed": False})
    closed_assessment = assess_case({"global_claim": True}, stability_spec={"multi_seed": True})

    assert_item(open_assessment, "global-claim", severity="high", status="open", score=0.20)
    assert_item(partial_assessment, "global-claim", severity="medium", status="partial", score=0.10)
    assert_item(closed_assessment, "global-claim", severity="none", status="closed", score=0.0)


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
