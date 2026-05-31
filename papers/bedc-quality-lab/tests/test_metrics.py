import numpy as np

from bedc_quality_lab.metrics import (
    approximate_identifiability_proxy,
    covariance_deviation,
    linear_identifiability_r2,
    orthogonality_error,
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
