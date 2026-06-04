import math

from bedc_quality_lab.cost_protocol import SCOPED_DEBT_ROWS
from bedc_quality_lab.debt import assess_debt, format_debt_items
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.latent_distribution import (
    CANONICAL_LATENT_DISTRIBUTION_KEYS,
    LatentDistributionSpec,
)
from bedc_quality_lab.mixing import canonical_mixing_families


def closed_metrics(**patch):
    return {
        "theorem3_bound_mse": 1.0,
        "actual_recovery_mse": 0.25,
        "bound_margin_mse": 0.75,
        "normalized_gap_d_mse": 0.10,
        "whitening_deviation_epsilon": 0.20,
    } | patch


def example_specs():
    return (
        closed_source_spec()
        | {
            "name": "gaussian-ou-toy-world",
            "sample_count": 384,
            "mixing": "sinusoidal_shear",
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


def closed_source_spec():
    return {
        "source_count": 3,
        "mixing": canonical_mixing_families(),
        "latent_distribution": {"family": "gaussian", "coverage_key": "gaussian"},
        "latent_distribution_coverage_keys": list(CANONICAL_LATENT_DISTRIBUTION_KEYS),
        "latent_dim": 2,
        "sample_count": 2048,
        "action_transition_identified": True,
        "global_claim": False,
    }


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
        "source",
        "source",
        "classifier",
        "verification",
        "generalization",
    ]
    assert [item.residue for item in assessment.items] == [
        "source-coverage",
        "mixing-family-coverage",
        "latent-distribution-gaussianity",
        "distribution-family-coverage",
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
        closed_source_spec() | source_spec,
        classifier_spec or {"name": "align-classifier", "training": "align-cov-mean"},
        stability_spec or {"name": "single-seed"},
    )


def assess_scoped_case(source_spec, classifier_spec=None, stability_spec=None):
    return assess_debt(
        closed_metrics(approx_identifiability_proxy=0.25),
        closed_source_spec() | source_spec,
        classifier_spec or {"name": "align-classifier", "training": "align-cov-mean"},
        stability_spec or {"name": "single-seed"},
        extra_rows=SCOPED_DEBT_ROWS,
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
    family_a, family_b, family_c, family_d = canonical_mixing_families()
    no_canonical_assessment = assess_case({"mixing": "not-canonical"})
    open_assessment = assess_case({"mixing": family_a})
    partial_two_assessment = assess_case({"mixing": [family_a, family_b]})
    partial_three_assessment = assess_case({"mixing": [family_a, family_b, family_c]})
    closed_assessment = assess_case({"mixing": [family_a, family_b, family_c, family_d]})

    assert_residue(
        no_canonical_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="high",
        status="open",
        score=0.22,
    )
    assert_residue(
        open_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="high",
        status="open",
        score=0.22,
    )
    assert_residue(
        partial_two_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="medium",
        status="partial",
        score=0.11,
    )
    assert_residue(
        partial_three_assessment,
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


def test_distribution_coverage_dedupes_and_never_closes_for_non_canonical_names():
    family_a, family_b, family_c, family_d = canonical_mixing_families()
    duplicate_assessment = assess_case({"mixing": [family_a, family_a, family_b]})
    mixed_assessment = assess_case({"mixing": [family_a, family_b, family_c, "not-canonical"]})
    non_canonical_only_assessment = assess_case(
        {"mixing": ["alpha", "beta", "gamma", "delta", "epsilon"]}
    )
    closed_assessment = assess_case({"mixing": [family_a, family_b, family_c, family_d, "not-canonical"]})

    assert_residue(
        duplicate_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="medium",
        status="partial",
        score=0.11,
    )
    assert_residue(
        mixed_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="medium",
        status="partial",
        score=0.11,
    )
    assert_residue(
        non_canonical_only_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="high",
        status="open",
        score=0.22,
    )
    assert_residue(
        closed_assessment,
        "mixing-family-coverage",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_debt_latent_gaussianity_closed_for_gaussian_open_for_nongaussian():
    gaussian = assess_case({"latent_distribution": LatentDistributionSpec.gaussian().to_source_spec()})
    laplace = assess_case({"latent_distribution": LatentDistributionSpec.laplace().to_source_spec()})
    missing_source = dict(closed_source_spec())
    missing_source.pop("latent_distribution")
    missing = assess_debt(
        closed_metrics(),
        missing_source,
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
    )

    assert_residue(
        gaussian,
        "latent-distribution-gaussianity",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        laplace,
        "latent-distribution-gaussianity",
        kind="source",
        severity="high",
        status="open",
        score=0.16,
    )
    assert_residue(
        missing,
        "latent-distribution-gaussianity",
        kind="source",
        severity="high",
        status="open",
        score=0.16,
    )


def test_debt_distribution_family_coverage_open_partial_closed():
    gaussian = LatentDistributionSpec.gaussian().to_source_spec()
    laplace = LatentDistributionSpec.laplace().to_source_spec()
    all_families = [
        {"coverage_key": key}
        for key in CANONICAL_LATENT_DISTRIBUTION_KEYS
    ]

    open_source = dict(closed_source_spec())
    open_source.pop("latent_distribution_coverage_keys")
    partial_source = dict(open_source)
    open_assessment = assess_debt(
        closed_metrics(),
        open_source | {"latent_distribution": gaussian},
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
    )
    partial_assessment = assess_debt(
        closed_metrics(),
        partial_source | {"latent_distribution": [gaussian, laplace]},
        {"name": "certified-search", "training": "certified"},
        {"multi_seed": True},
    )
    closed_assessment = assess_case({"latent_distribution": all_families})

    assert_residue(
        open_assessment,
        "distribution-family-coverage",
        kind="source",
        severity="high",
        status="open",
        score=0.24,
    )
    assert_residue(
        partial_assessment,
        "distribution-family-coverage",
        kind="source",
        severity="medium",
        status="partial",
        score=0.12,
    )
    assert_residue(
        closed_assessment,
        "distribution-family-coverage",
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


def test_optimizer_certificate_steps_pin_closed_partial_open_statuses():
    open_assessment = assess_case({}, {"output_dim": 2, "optimizer_certificate_steps": 20})
    partial_assessment = assess_case({}, {"output_dim": 2, "optimizer_certificate_steps": 100})
    nearly_closed_assessment = assess_case({}, {"output_dim": 2, "optimizer_certificate_steps": 500})
    closed_assessment = assess_case({}, {"output_dim": 2, "optimizer_certificate_steps": 2000})

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
        nearly_closed_assessment,
        "optimizer-certificate",
        kind="classifier",
        severity="low",
        status="partial",
        score=0.05,
    )
    assert_residue(
        closed_assessment,
        "optimizer-certificate",
        kind="classifier",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_dimension_match_closed_partial_open_for_encoder_output_dim():
    closed_assessment = assess_scoped_case({"latent_dim": 2}, {"output_dim": 2, "training": "certified"})
    partial_assessment = assess_scoped_case({"latent_dim": 2}, {"output_dim": 1, "training": "certified"})
    open_assessment = assess_scoped_case({"latent_dim": 2}, {"output_dim": 4, "training": "certified"})

    assert_residue(
        closed_assessment,
        "dimension-match",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )
    assert_residue(
        partial_assessment,
        "dimension-match",
        kind="source",
        severity="medium",
        status="partial",
        score=0.09,
    )
    assert_residue(
        open_assessment,
        "dimension-match",
        kind="source",
        severity="high",
        status="open",
        score=0.18,
    )


def test_dimension_match_missing_or_invalid_dimensions_fail_open():
    missing_latent = assess_debt(
        closed_metrics(),
        {},
        {"output_dim": 2},
        {"multi_seed": True},
        extra_rows=SCOPED_DEBT_ROWS,
    )
    missing_output = assess_scoped_case({"latent_dim": 2}, {"training": "certified"})
    invalid_latent = assess_scoped_case({"latent_dim": 0}, {"output_dim": 2, "training": "certified"})
    invalid_output = assess_scoped_case({"latent_dim": 2}, {"output_dim": "2", "training": "certified"})

    for assessment in (missing_latent, missing_output, invalid_latent, invalid_output):
        assert_residue(
            assessment,
            "dimension-match",
            kind="source",
            severity="high",
            status="open",
            score=0.18,
        )


def test_action_transition_identified_closes_row():
    assessment = assess_scoped_case({"latent_dim": 2, "action_transition_identified": True}, {"output_dim": 2})

    assert_residue(
        assessment,
        "action-transition-identification",
        kind="source",
        severity="none",
        status="closed",
        score=0.0,
    )


def test_action_transition_false_opens_row_and_formats_ledger_gap():
    source_spec = closed_source_spec() | {
        "latent_dim": 2,
        "action_transition_identified": False,
    }
    classifier_spec = {"output_dim": 2, "training": "certified"}
    stability_spec = {"multi_seed": True}
    assessment = assess_debt(
        closed_metrics(),
        source_spec,
        classifier_spec,
        stability_spec,
        extra_rows=SCOPED_DEBT_ROWS,
    )
    gaps = derive_ledger_gaps(closed_metrics(), source_spec, classifier_spec, stability_spec, assessment)

    assert_residue(
        assessment,
        "action-transition-identification",
        kind="source",
        severity="high",
        status="open",
        score=0.16,
    )
    assert (
        "kind=source; residue=action-transition-identification; severity=high; status=open"
        in format_ledger_gaps(gaps)
    )


def test_action_transition_missing_or_invalid_values_fail_open_and_format_ledger_gap():
    classifier_spec = {"output_dim": 2, "training": "certified"}
    stability_spec = {"multi_seed": True}
    missing_source = closed_source_spec() | {"latent_dim": 2}
    missing_source.pop("action_transition_identified")
    cases = (
        missing_source,
        closed_source_spec() | {"latent_dim": 2, "action_transition_identified": None},
        closed_source_spec() | {"latent_dim": 2, "action_transition_identified": "true"},
    )

    for source_spec in cases:
        assessment = assess_debt(
            closed_metrics(),
            source_spec,
            classifier_spec,
            stability_spec,
            extra_rows=SCOPED_DEBT_ROWS,
        )
        gaps = derive_ledger_gaps(closed_metrics(), source_spec, classifier_spec, stability_spec, assessment)

        assert_residue(
            assessment,
            "action-transition-identification",
            kind="source",
            severity="high",
            status="open",
            score=0.16,
        )
        assert (
            "kind=source; residue=action-transition-identification; severity=high; status=open"
            in format_ledger_gaps(gaps)
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
        closed_metrics(theorem3_bound_mse=1.0, actual_recovery_mse=1.0, bound_margin_mse=0.0),
        closed_source_spec(),
        {"name": "certified-search", "training": "certified", "output_dim": 2},
        {"multi_seed": True},
    )
    open_assessment = assess_debt(
        closed_metrics(theorem3_bound_mse=1.0, actual_recovery_mse=2.0, bound_margin_mse=-1.0),
        closed_source_spec(),
        {"name": "certified-search", "training": "certified", "output_dim": 2},
        {"multi_seed": True},
    )
    missing_assessment = assess_debt(
        {},
        closed_source_spec(),
        {"name": "certified-search", "training": "certified", "output_dim": 2},
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

    assert len(rows) == 9
    for row in rows:
        assert "kind=" in row
        assert "residue=" in row
        assert "severity=" in row
        assert "status=" in row
        assert "score=" in row
