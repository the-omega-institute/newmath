import numpy as np
import pytest

from bedc_quality_lab.identifiability_bound import (
    alignment_gap_delta,
    bound_margin,
    empirical_alignment_loss,
    identifiability_bound_metrics,
    normalized_gap_d,
    orthogonal_recovery_error,
    procrustes_q,
    theorem3_bound,
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

    assert orthogonal_recovery_error(z, z) == pytest.approx(0.0, abs=1e-12)


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

    assert orthogonal_recovery_error(h, z) == pytest.approx(0.0, abs=1e-12)
    assert recovered.T @ recovered == pytest.approx(np.eye(2), abs=1e-12)


def test_nonlinear_mixing_has_positive_recovery_error():
    z = fixture_latents()
    h = np.column_stack([z[:, 0], z[:, 1] ** 2])

    assert orthogonal_recovery_error(h, z) > 0.25


def test_rho_denominator_fails_closed_near_zero_or_one():
    with pytest.raises(ValueError):
        normalized_gap_d(0.1, 1e-12)
    with pytest.raises(ValueError):
        normalized_gap_d(0.1, 1.0 - 1e-12)


def test_theorem3_bound_formula_is_pinned():
    d = 0.25
    epsilon = 0.40

    assert theorem3_bound(d, epsilon) == pytest.approx(d + (epsilon + d) ** 2)


def test_bound_margin_is_bound_minus_actual_and_may_be_negative():
    assert bound_margin(0.2, 0.7) == pytest.approx(-0.5)


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

    alignment_loss = empirical_alignment_loss(h, h_pair)
    epsilon = whitening_deviation_epsilon(h)
    delta = alignment_gap_delta(alignment_loss, rho)
    d_value = normalized_gap_d(delta, rho)
    metrics = identifiability_bound_metrics(h, h_pair, z, rho)
    expected_bound = d_value + (epsilon + d_value) ** 2

    assert alignment_loss == pytest.approx(7.0 / 6.0)
    assert epsilon == pytest.approx(np.sqrt(10.0 / 9.0))
    assert delta == pytest.approx(2.0 / 3.0)
    assert d_value == pytest.approx((2.0 / 3.0) / (2.0 * rho * (1.0 - rho)))
    assert set(metrics) == {
        "alignment_loss",
        "alignment_gap_delta",
        "whitening_deviation_epsilon",
        "normalized_gap_d",
        "theorem3_bound",
        "actual_recovery_error",
        "bound_margin",
    }
    assert metrics["alignment_loss"] == pytest.approx(alignment_loss)
    assert metrics["alignment_gap_delta"] == pytest.approx(delta)
    assert metrics["whitening_deviation_epsilon"] == pytest.approx(epsilon)
    assert metrics["normalized_gap_d"] == pytest.approx(d_value)
    assert metrics["theorem3_bound"] == pytest.approx(expected_bound)
    assert metrics["actual_recovery_error"] == pytest.approx(0.0, abs=1e-12)
    assert metrics["bound_margin"] == pytest.approx(
        metrics["theorem3_bound"] - metrics["actual_recovery_error"]
    )


def test_invalid_inputs_fail_closed():
    z = fixture_latents()
    bad = z.copy()
    bad[0, 0] = np.nan

    with pytest.raises(ValueError):
        orthogonal_recovery_error(z[:-1], z)
    with pytest.raises(ValueError):
        empirical_alignment_loss(z, z[:-1])
    with pytest.raises(ValueError):
        whitening_deviation_epsilon(bad)
    with pytest.raises(ValueError):
        alignment_gap_delta(-0.1, 0.82)
    with pytest.raises(ValueError):
        theorem3_bound(-0.1, 0.2)
    with pytest.raises(ValueError):
        identifiability_bound_metrics(z, bad, z, 0.82)
