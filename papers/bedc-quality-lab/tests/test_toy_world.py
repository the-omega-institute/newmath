import numpy as np
import pytest

from bedc_quality_lab.mixing import DEFAULT_MIXING, canonical_mixing_families, mix_latents
from bedc_quality_lab.toy_world import make_ou_pair, make_toy_batch
from bedc_quality_lab.transition import TransitionKernelSpec, make_transition_pair


def test_toy_world_ou_pair_has_expected_shape_and_correlation():
    rho = 0.78
    batch = make_toy_batch(4000, rho=rho, seed=101)
    assert batch.z.shape == (4000, 2)
    assert batch.z_pair.shape == (4000, 2)
    assert batch.x.shape == (4000, 2)
    assert batch.x_pair.shape == (4000, 2)

    observed = np.mean(batch.z * batch.z_pair, axis=0)
    assert np.allclose(observed, np.array([rho, rho]), atol=0.06)


def test_scalar_make_ou_pair_delegates_without_changing_values():
    z = np.array([[1.0, -2.0], [0.25, 0.5]], dtype=np.float64)
    rho = 0.41

    observed = make_ou_pair(z, rho=rho, seed=19)
    expected = make_transition_pair(z, TransitionKernelSpec.isotropic(rho, latent_dim=2), seed=19)

    assert observed == pytest.approx(expected)


def test_make_toy_batch_accepts_transition_kernel_for_per_axis_rho():
    spec = TransitionKernelSpec(rho_by_axis=(0.95, 0.3))
    batch = make_toy_batch(5000, transition_kernel=spec, seed=303)

    observed = np.mean(batch.z * batch.z_pair, axis=0)

    assert np.allclose(observed, np.array([0.95, 0.3]), atol=0.06)


def test_make_toy_batch_routes_default_mixing_to_both_observation_paths():
    batch = make_toy_batch(32, seed=404)

    assert batch.x == pytest.approx(mix_latents(batch.z, DEFAULT_MIXING))
    assert batch.x_pair == pytest.approx(mix_latents(batch.z_pair, DEFAULT_MIXING))


def test_make_toy_batch_routes_each_canonical_mixing_family():
    for family in canonical_mixing_families():
        batch = make_toy_batch(32, seed=505, mixing=family)

        assert batch.x == pytest.approx(mix_latents(batch.z, family))
        assert batch.x_pair == pytest.approx(mix_latents(batch.z_pair, family))


def test_make_toy_batch_rejects_unknown_mixing_family():
    with pytest.raises(ValueError, match="unknown mixing family"):
        make_toy_batch(8, mixing="not-canonical")
