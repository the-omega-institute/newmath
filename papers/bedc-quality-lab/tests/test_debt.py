import math

from bedc_quality_lab.debt import assess_debt, format_debt_items


def closed_metrics(**patch):
    return {
        "theorem3_bound": 1.0,
        "actual_recovery_error": 0.25,
        "bound_margin": 0.75,
        "normalized_gap_d": 0.10,
        "whitening_deviation_epsilon": 0.20,
    } | patch


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


def test_debt_assessment_has_required_bounded_categories():
    source_spec, classifier_spec, stability_spec = example_specs()
    assessment = assess_debt(
        closed_metrics(approx_identifiability_proxy=0.8),
        source_spec,
        classifier_spec,
        stability_spec,
    )

    assert [item.kind for item in assessment.items] == [
        "source",
        "source",
        "source",
        "source",
        "classifier",
        "verification",
        "generalization",
    ]
    assert [item.residue for item in assessment.items] == [
        "source-coverage",
        "mixing-family-coverage",
        "finite-sample-support",
        "transition-isotropy",
        "optimizer-certificate",
        "theorem3-bound-margin",
        "global-claim-boundary",
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


def assert_residue(assessment, residue, *, kind, severity, status, score):
    matches = [item for item in assessment.items if item.residue == residue]
    assert len(matches) == 1
    item = matches[0]
    assert item.kind == kind
    assert item.severity == severity
    assert item.status == status
    assert math.isclose(item.score, score, rel_tol=0.0, abs_tol=1e-12)


def assess_case(source_spec, classifier_spec=None, stability_spec=None):
    return assess_debt(
        closed_metrics(approx_identifiability_proxy=0.25),
        source_spec,
        classifier_spec or {"name": "align-classifier", "training": "align-cov-mean"},
        stability_spec or {"name": "single-seed"},
    )


def test_source_coverage_thresholds_pin_closed_partial_open_statuses():
    open_assessment = assess_case({"source_count": 1})
    partial_assessment = assess_case({"source_count": 2})
    closed_assessment = assess_case({"source_count": 3})

    assert_residue(open_assessment, "source-coverage", kind="source", severity="high", status="open", score=0.18)
    assert_residue(
        partial_assessment,
        "source-coverage",
        kind="source",
        severity="medium",
        status="partial",
        score=0.09,
    )
    assert_residue(
        closed_assessment,
        "source-coverage",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_distribution_coverage_thresholds_pin_closed_partial_open_statuses():
    open_assessment = assess_case({"mixing": "single-family"})
    partial_assessment = assess_case({"mixing": ["a", "b"]})
    closed_assessment = assess_case({"mixing": ["a", "b", "c"]})

    assert_residue(
        open_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="high",
        status="open",
        score=0.22,
    )
    assert_residue(
        partial_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="medium",
        status="partial",
        score=0.11,
    )
    assert_residue(
        closed_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_finite_sample_thresholds_pin_all_score_bands():
    below_support = assess_case({"sample_count": 511})
    weak_support = assess_case({"sample_count": 512})
    partial_support = assess_case({"sample_count": 1024})
    closed_support = assess_case({"sample_count": 2048})

    assert_residue(
        below_support,
        "finite-sample-support",
        kind="source",
        severity="high",
        status="open",
        score=0.20,
    )
    assert_residue(
        weak_support,
        "finite-sample-support",
        kind="source",
        severity="medium",
        status="partial",
        score=0.10,
    )
    assert_residue(
        partial_support,
        "finite-sample-support",
        kind="source",
        severity="low",
        status="partial",
        score=0.05,
    )
    assert_residue(
        closed_support,
        "finite-sample-support",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_transition_isotropy_row_closes_for_scalar_and_isotropic_metadata():
    scalar_metadata = assess_case({})
    isotropic = assess_case(
        {
            "transition_kernel": {
                "family": "ornstein-uhlenbeck",
                "rho_by_axis": [0.9, 0.9],
                "noise_family": "gaussian",
                "isotropic": True,
                "anisotropy_gap": 0.0,
            }
        }
    )

    assert_residue(
        scalar_metadata,
        "transition-isotropy",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        isotropic,
        "transition-isotropy",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_transition_isotropy_row_opens_from_anisotropic_transition_metadata():
    partial_assessment = assess_case(
        {
            "transition_kernel": {
                "isotropic": False,
                "anisotropy_gap": 0.3,
            }
        }
    )
    open_assessment = assess_case(
        {
            "transition_kernel": {
                "isotropic": False,
                "anisotropy_gap": 0.8,
            }
        }
    )

    assert_residue(
        partial_assessment,
        "transition-isotropy",
        kind="source",
        severity="medium",
        status="partial",
        score=0.072,
    )
    assert_residue(
        open_assessment,
        "transition-isotropy",
        kind="source",
        severity="high",
        status="open",
        score=0.12,
    )


def test_optimization_certified_deterministic_and_open_training_statuses():
    open_assessment = assess_case({}, {"name": "tiny-mlp", "training": "align-cov-mean"})
    partial_assessment = assess_case(
        {},
        {"name": "standardized-observation", "training": "deterministic-standardization"},
    )
    certified_assessment = assess_case({}, {"name": "certified-search", "training": "align"})
    exhaustive_assessment = assess_case({}, {"name": "finite", "training": "exhaustive-grid"})

    assert_residue(
        open_assessment,
        "optimizer-certificate",
        kind="classifier",
        severity="high",
        status="open",
        score=0.20,
    )
    assert_residue(
        partial_assessment,
        "optimizer-certificate",
        kind="classifier",
        severity="medium",
        status="partial",
        score=0.10,
    )
    assert_residue(
        certified_assessment,
        "optimizer-certificate",
        kind="classifier",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        exhaustive_assessment,
        "optimizer-certificate",
        kind="classifier",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_global_claim_multi_seed_thresholds_pin_closed_partial_open_statuses():
    scoped_assessment = assess_case({"global_claim": False}, stability_spec={"multi_seed": True})
    missing_assessment = assess_case({}, stability_spec={"multi_seed": False})
    partial_assessment = assess_case({"global_claim": True}, stability_spec={"multi_seed": False})
    closed_assessment = assess_case({"global_claim": True}, stability_spec={"multi_seed": True})

    assert_residue(
        scoped_assessment,
        "global-claim-boundary",
        kind="generalization",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        missing_assessment,
        "global-claim-boundary",
        kind="generalization",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        partial_assessment,
        "global-claim-boundary",
        kind="generalization",
        severity="medium",
        status="partial",
        score=0.10,
    )
    assert_residue(
        closed_assessment,
        "global-claim-boundary",
        kind="generalization",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_theorem_bound_margin_thresholds_pin_closed_and_open_statuses():
    closed_assessment = assess_case({}, stability_spec={"multi_seed": True})
    zero_assessment = assess_debt(
        closed_metrics(theorem3_bound=1.0, actual_recovery_error=1.0, bound_margin=0.0),
        {"source_count": 3, "mixing": ["a", "b", "c"], "sample_count": 2048},
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
    )
    open_assessment = assess_debt(
        closed_metrics(theorem3_bound=1.0, actual_recovery_error=2.0, bound_margin=-1.0),
        {"source_count": 3, "mixing": ["a", "b", "c"], "sample_count": 2048},
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
    )
    missing_assessment = assess_debt(
        {},
        {"source_count": 3, "mixing": ["a", "b", "c"], "sample_count": 2048},
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
    )

    assert_residue(
        closed_assessment,
        "theorem3-bound-margin",
        kind="verification",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        zero_assessment,
        "theorem3-bound-margin",
        kind="verification",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        open_assessment,
        "theorem3-bound-margin",
        kind="verification",
        severity="high",
        status="open",
        score=0.20,
    )
    assert_residue(
        missing_assessment,
        "theorem3-bound-margin",
        kind="verification",
        severity="high",
        status="open",
        score=0.20,
    )
    assert math.isclose(open_assessment.debt_total, 0.20, rel_tol=0.0, abs_tol=1e-12)


def test_debt_formatter_emits_canonical_keys():
    source_spec, classifier_spec, stability_spec = example_specs()
    assessment = assess_debt(closed_metrics(), source_spec, classifier_spec, stability_spec)

    rows = format_debt_items(assessment)

    assert len(rows) == 7
    for row in rows:
        assert "kind=" in row
        assert "residue=" in row
        assert "severity=" in row
        assert "status=" in row
        assert "score=" in row
