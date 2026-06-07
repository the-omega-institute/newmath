import numpy as np

from bedc_quality_lab.toy_world import make_toy_batch


def test_toy_world_ou_pair_has_expected_shape_and_correlation():
    rho = 0.78
    batch = make_toy_batch(4000, rho=rho, seed=101)
    assert batch.z.shape == (4000, 2)
    assert batch.z_pair.shape == (4000, 2)
    assert batch.x.shape == (4000, 2)
    assert batch.x_pair.shape == (4000, 2)

    observed = np.mean(batch.z * batch.z_pair, axis=0)
    assert np.allclose(observed, np.array([rho, rho]), atol=0.06)
