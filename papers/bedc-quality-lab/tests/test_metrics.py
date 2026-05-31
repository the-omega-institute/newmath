import numpy as np

from bedc_quality_lab.metrics import (
    approximate_identifiability_proxy,
    covariance_deviation,
    linear_identifiability_r2,
    orthogonality_error,
    quality_components,
)


def test_metrics_linear_recovery_and_shuffle_direction():
    rng = np.random.default_rng(7)
    z = rng.normal(size=(256, 2))
    h = z @ np.array([[1.2, -0.4], [0.3, 0.9]]) + np.array([0.1, -0.2])
    shuffled = h[rng.permutation(h.shape[0])]

    good_r2 = linear_identifiability_r2(h, z)
    shuffled_r2 = linear_identifiability_r2(shuffled, z)

    assert good_r2 > 0.98
    assert shuffled_r2 < 0.15
    assert approximate_identifiability_proxy(h, z) > approximate_identifiability_proxy(shuffled, z)
    assert orthogonality_error(h) >= 0.0
    assert covariance_deviation(h) >= 0.0


def test_quality_components_follow_identity_and_debt_monotonicity():
    metrics = {
        "linear_identifiability_r2": 0.90,
        "approx_identifiability_proxy": 0.80,
    }
    classifier_spec = {
        "name": "tiny-mlp-2-128-128-2",
        "output_dim": 2,
        "training": "align-cov-mean",
    }

    low_debt = quality_components(metrics, 0.10, classifier_spec)
    high_debt = quality_components(metrics, 0.30, classifier_spec)

    assert np.isclose(
        low_debt["quality_q"],
        low_debt["quality_benefit"] - low_debt["quality_cost"] - low_debt["quality_debt"],
    )
    assert high_debt["quality_q"] < low_debt["quality_q"]


def test_quality_components_clamp_benefit_and_debt():
    high_values = quality_components(
        {"linear_identifiability_r2": 1.4, "approx_identifiability_proxy": 1.2},
        1.7,
        {"output_dim": 1, "training": ""},
    )
    low_values = quality_components(
        {"linear_identifiability_r2": -0.4, "approx_identifiability_proxy": -0.2},
        -0.3,
        {"output_dim": 1, "training": ""},
    )

    assert high_values["quality_benefit"] == 1.0
    assert high_values["quality_debt"] == 1.0
    assert low_values["quality_benefit"] == 0.0
    assert low_values["quality_debt"] == 0.0


def test_quality_components_output_dimension_cost_cap_and_fallback():
    metrics = {"linear_identifiability_r2": 0.0, "approx_identifiability_proxy": 0.0}

    capped = quality_components(metrics, 0.0, {"output_dim": 20, "training": ""})
    fallback = quality_components(metrics, 0.0, {"output_dim": "wide", "training": ""})

    assert np.isclose(capped["quality_cost"], 0.09)
    assert np.isclose(fallback["quality_cost"], 0.02)


def test_quality_components_align_training_has_higher_cost_than_non_align():
    metrics = {"linear_identifiability_r2": 0.0, "approx_identifiability_proxy": 0.0}

    align = quality_components(metrics, 0.0, {"output_dim": 2, "training": "align-cov-mean"})
    non_align = quality_components(
        metrics,
        0.0,
        {"output_dim": 2, "training": "deterministic-standardization"},
    )

    assert np.isclose(align["quality_cost"], 0.06)
    assert np.isclose(non_align["quality_cost"], 0.03)
    assert np.isclose(align["quality_cost"] - non_align["quality_cost"], 0.03)
