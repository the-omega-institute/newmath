import numpy as np
import pytest

from bedc_quality_lab.identifiability_bound import (
    actual_recovery_normalized,
    alignment_gap_delta_mse,
    alignment_gap_delta_normalized,
    alignment_loss_mse,
    alignment_loss_normalized,
    bound_margin_mse,
    bound_margin_normalized,
    covariance_trace,
    identifiability_bound_metrics,
    normalized_gap_d_mse,
    orthogonal_recovery_mse,
    procrustes_q,
    theorem3_bound_mse,
    theorem3_bound_normalized,
    whitening_deviation_epsilon,
)


def fixture_latents():
    return np.array(
        [
            [-2.0, -1.0],
            [-1.0, 0.5],
            [0.0, 1.5],
            [1.0, -0.5],
            [2.0, 0.25],
            [3.0, 1.0],
        ],
        dtype=np.float64,
    )


def test_identity_representation_has_near_zero_recovery_error():
    z = fixture_latents()

    metrics = identifiability_bound_metrics(z, z, z, 0.82)

    assert orthogonal_recovery_mse(z, z) == pytest.approx(0.0, abs=1e-12)
    assert metrics["actual_recovery_mse"] <= 1e-10


def test_orthogonal_transform_recovers_with_orthogonal_q():
    z = fixture_latents()
    theta = 0.37
    q = np.array(
        [
            [np.cos(theta), -np.sin(theta)],
            [np.sin(theta), np.cos(theta)],
        ],
        dtype=np.float64,
    )
    h = z @ q.T
    recovered = procrustes_q(h, z)
    metrics = identifiability_bound_metrics(h, h, z, 0.82)

    assert orthogonal_recovery_mse(h, z) == pytest.approx(0.0, abs=1e-12)
    assert metrics["actual_recovery_mse"] <= 1e-10
    assert recovered.T @ recovered == pytest.approx(np.eye(2), abs=1e-12)


def test_nonlinear_mixing_has_positive_recovery_error():
    z = fixture_latents()
    h = np.column_stack([z[:, 0], z[:, 1] ** 2])
    metrics = identifiability_bound_metrics(h, h, z, 0.82)

    assert orthogonal_recovery_mse(h, z) > 0.25
    assert metrics["actual_recovery_mse"] > 0.25


def test_rho_denominator_fails_closed_near_zero_or_one():
    with pytest.raises(ValueError):
        normalized_gap_d_mse(0.1, 1e-12)
    with pytest.raises(ValueError):
        normalized_gap_d_mse(0.1, 1.0 - 1e-12)


def test_theorem3_bound_formula_is_pinned():
    d = 0.25
    epsilon = 0.40

    assert theorem3_bound_mse(d, epsilon) == pytest.approx(d + (epsilon + d) ** 2)


def test_bound_margin_is_bound_minus_actual_and_may_be_negative():
    assert bound_margin_mse(0.2, 0.7) == pytest.approx(-0.5)
    assert bound_margin_normalized(0.2, 0.7) == pytest.approx(-0.5)


def test_identifiability_bound_success_path_formulas_are_pinned():
    h = np.array(
        [
            [0.0, 0.0],
            [2.0, 0.0],
            [0.0, 2.0],
        ],
        dtype=np.float64,
    )
    h_pair = np.array(
        [
            [-1.0, 0.0],
            [2.0, 2.0],
            [-1.0, 1.0],
        ],
        dtype=np.float64,
    )
    z = h.copy()
    rho = 0.75

    alignment_mse = alignment_loss_mse(h, h_pair)
    alignment_normalized = alignment_loss_normalized(h, h_pair)
    trace = covariance_trace(h)
    epsilon = whitening_deviation_epsilon(h)
    delta_mse = alignment_gap_delta_mse(alignment_mse, rho, trace)
    delta_normalized = alignment_gap_delta_normalized(alignment_normalized, rho)
    d_value = normalized_gap_d_mse(delta_mse, rho)
    metrics = identifiability_bound_metrics(h, h_pair, z, rho)
    expected_bound = d_value + (epsilon + d_value) ** 2
    expected_bound_normalized = expected_bound / trace

    assert alignment_mse == pytest.approx(7.0 / 3.0)
    assert alignment_normalized == pytest.approx(7.0 / 6.0)
    assert trace == pytest.approx(8.0 / 3.0)
    assert epsilon == pytest.approx(np.sqrt(10.0 / 9.0))
    assert delta_mse == pytest.approx(1.0)
    assert delta_normalized == pytest.approx(2.0 / 3.0)
    assert d_value == pytest.approx(1.0 / (2.0 * rho * (1.0 - rho)))
    assert set(metrics) == {
        "alignment_loss_mse",
        "covariance_trace",
        "alignment_gap_delta_mse",
        "normalized_gap_d_mse",
        "whitening_deviation_epsilon",
        "theorem3_bound_mse",
        "actual_recovery_mse",
        "bound_margin_mse",
        "alignment_loss_normalized",
        "alignment_gap_delta_normalized",
        "actual_recovery_normalized",
        "theorem3_bound_normalized",
        "bound_margin_normalized",
    }
    assert "actual_recovery_error" not in metrics
    assert "theorem3_bound" not in metrics
    assert "bound_margin" not in metrics
    assert metrics["alignment_loss_mse"] == pytest.approx(alignment_mse)
    assert metrics["covariance_trace"] == pytest.approx(trace)
    assert metrics["alignment_gap_delta_mse"] == pytest.approx(delta_mse)
    assert metrics["normalized_gap_d_mse"] == pytest.approx(d_value)
    assert metrics["whitening_deviation_epsilon"] == pytest.approx(epsilon)
    assert metrics["theorem3_bound_mse"] == pytest.approx(expected_bound)
    assert metrics["theorem3_bound_mse"] >= 0.0
    assert metrics["actual_recovery_mse"] == pytest.approx(0.0, abs=1e-12)
    assert metrics["bound_margin_mse"] == pytest.approx(
        metrics["theorem3_bound_mse"] - metrics["actual_recovery_mse"]
    )
    assert metrics["alignment_loss_normalized"] == pytest.approx(alignment_normalized)
    assert metrics["alignment_gap_delta_normalized"] == pytest.approx(delta_normalized)
    assert metrics["actual_recovery_normalized"] == pytest.approx(actual_recovery_normalized(h, z))
    assert metrics["theorem3_bound_normalized"] == pytest.approx(expected_bound_normalized)
    assert metrics["theorem3_bound_normalized"] == pytest.approx(
        theorem3_bound_normalized(metrics["theorem3_bound_mse"], trace)
    )
    assert metrics["bound_margin_normalized"] == pytest.approx(
        metrics["theorem3_bound_normalized"] - metrics["actual_recovery_normalized"]
    )


def test_invalid_inputs_fail_closed():
    z = fixture_latents()
    bad = z.copy()
    bad[0, 0] = np.nan

    with pytest.raises(ValueError):
        orthogonal_recovery_mse(z[:-1], z)
    with pytest.raises(ValueError):
        alignment_loss_mse(z, z[:-1])
    with pytest.raises(ValueError):
        whitening_deviation_epsilon(bad)
    with pytest.raises(ValueError):
        alignment_gap_delta_mse(-0.1, 0.82, 1.0)
    with pytest.raises(ValueError):
        theorem3_bound_mse(-0.1, 0.2)
    with pytest.raises(ValueError):
        identifiability_bound_metrics(z, bad, z, 0.82)
