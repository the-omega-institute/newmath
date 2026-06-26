import numpy as np
import pytest

from bedc_quality_lab.mixing import (
    CANONICAL_MIXING_FAMILIES,
    DEFAULT_MIXING,
    canonical_mixing_families,
    covered_canonical_mixing_families,
    mix_latents,
)


def test_canonical_names_and_default_are_stable():
    assert CANONICAL_MIXING_FAMILIES == (
        "spiral",
        "sinusoidal_shear",
        "parabolic_shear",
        "realnvp_coupling",
    )
    assert canonical_mixing_families() == CANONICAL_MIXING_FAMILIES
    assert DEFAULT_MIXING == "sinusoidal_shear"


def test_each_family_is_shape_preserving_finite_and_deterministic():
    z = np.array(
        [
            [0.0, 0.0],
            [1.0, -0.5],
            [-0.75, 1.25],
            [2.0, 0.5],
        ],
        dtype=np.float64,
    )

    for family in canonical_mixing_families():
        left = mix_latents(z, family)
        right = mix_latents(z, family)

        assert left.shape == z.shape
        assert left.dtype == np.float64
        assert np.all(np.isfinite(left))
        assert left == pytest.approx(right)


def test_family_outputs_are_visibly_distinct():
    z = np.array(
        [
            [0.5, -1.0],
            [1.25, 0.75],
            [-1.5, 0.25],
            [2.0, -0.25],
        ],
        dtype=np.float64,
    )
    outputs = [mix_latents(z, family) for family in canonical_mixing_families()]

    for index, left in enumerate(outputs):
        for right in outputs[index + 1 :]:
            assert not np.allclose(left, right)


def test_invalid_shape_and_unknown_name_reject():
    with pytest.raises(ValueError, match="shape"):
        mix_latents(np.array([1.0, 2.0]), DEFAULT_MIXING)
    with pytest.raises(ValueError, match="shape"):
        mix_latents(np.ones((2, 3)), DEFAULT_MIXING)
    with pytest.raises(ValueError, match="unknown mixing family"):
        mix_latents(np.ones((2, 2)), "not-canonical")


def test_covered_canonical_mixing_families_dedupes_and_ignores_unknown_values():
    assert covered_canonical_mixing_families(
        ["not-canonical", "parabolic_shear", "spiral", "spiral"]
    ) == ("spiral", "parabolic_shear")
    assert covered_canonical_mixing_families("realnvp_coupling") == ("realnvp_coupling",)
    assert covered_canonical_mixing_families(["not-canonical", 3, None]) == ()
