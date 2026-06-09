import math

import numpy as np
import pytest

from bedc_quality_lab.transition import TransitionKernelSpec, make_transition_pair


def test_transition_spec_projects_ou_gaussian_source_surface():
    spec = TransitionKernelSpec(rho_by_axis=(0.9, 0.6))

    assert spec.family == "ornstein-uhlenbeck"
    assert spec.noise_family == "gaussian"
    assert spec.is_isotropic() is False
    assert spec.anisotropy_gap() == pytest.approx(0.3)
    assert spec.to_source_spec()["rho_by_axis"] == [0.9, 0.6]
    assert spec.to_source_spec()["eigenvalue_interleaving"]["boundary"] == (
        "Gaussian latent + anisotropic transition; transition noise is Gaussian."
    )


def test_transition_spec_isotropy_tolerance_boundary():
    spec = TransitionKernelSpec(rho_by_axis=(0.9, 0.9000000001))

    assert spec.is_isotropic(tolerance=1e-9)
    assert not spec.is_isotropic(tolerance=1e-12)
    with pytest.raises(ValueError, match="tolerance"):
        spec.is_isotropic(tolerance=-1.0)


def test_make_transition_pair_matches_per_axis_formula():
    z = np.array([[1.0, -2.0], [0.5, 0.25]], dtype=np.float64)
    spec = TransitionKernelSpec(rho_by_axis=(0.5, -0.25))
    rng = np.random.default_rng(7)
    eta = rng.normal(size=z.shape)
    rho = np.array([0.5, -0.25], dtype=np.float64)
    expected = z * rho + eta * np.sqrt(1.0 - rho * rho)

    observed = make_transition_pair(z, spec, seed=7)

    assert observed.dtype == np.float64
    assert observed == pytest.approx(expected)


@pytest.mark.parametrize("rho", [math.inf, -math.inf, math.nan, -1.0, 1.0])
def test_transition_spec_non_finite_or_out_of_range_rho_fails_closed(rho):
    with pytest.raises(ValueError):
        TransitionKernelSpec(rho_by_axis=(0.9, rho))


def test_make_transition_pair_validates_shape_and_dimension():
    spec = TransitionKernelSpec(rho_by_axis=(0.9, 0.6))
    with pytest.raises(ValueError, match="matrix"):
        make_transition_pair(np.array([1.0, 2.0]), spec, seed=1)
    with pytest.raises(ValueError, match="column count"):
        make_transition_pair(np.ones((4, 3)), spec, seed=1)
    with pytest.raises(ValueError, match="finite"):
        make_transition_pair(np.array([[1.0, math.nan]]), spec, seed=1)
