import numpy as np
import pytest

from bedc_quality_lab.latent_distribution import (
    CANONICAL_LATENT_DISTRIBUTION_ARMS,
    CANONICAL_LATENT_DISTRIBUTION_KEYS,
    LatentDistributionSpec,
)
from bedc_quality_lab.toy_world import make_latents


def test_latent_distribution_gaussian_matches_default_toy_world():
    observed = make_latents(128, seed=123)
    expected = LatentDistributionSpec.gaussian().sample(128, seed=123)

    assert observed == pytest.approx(expected)


def test_latent_distribution_specs_are_deterministic_finite_and_normalized():
    assert len(CANONICAL_LATENT_DISTRIBUTION_ARMS) == 9
    assert len(CANONICAL_LATENT_DISTRIBUTION_KEYS) == 9
    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS:
        first = spec.sample(4096, seed=544)
        second = spec.sample(4096, seed=544)

        assert first.shape == (4096, 2)
        assert np.all(np.isfinite(first))
        assert first == pytest.approx(second)
        assert np.mean(first, axis=0) == pytest.approx(np.zeros(2), abs=1e-12)
        assert np.std(first, axis=0) == pytest.approx(np.ones(2), abs=1e-12)


def test_latent_distribution_rejects_unknown_family_or_bad_shape():
    with pytest.raises(ValueError, match="unknown latent distribution family"):
        LatentDistributionSpec("not-canonical", None)
    with pytest.raises(ValueError, match="does not accept"):
        LatentDistributionSpec("gaussian", 1.0)
    with pytest.raises(ValueError, match="greater than 2"):
        LatentDistributionSpec.student_t(df=2)
    with pytest.raises(ValueError, match="positive"):
        LatentDistributionSpec.generalized_normal(alpha=0)
    with pytest.raises(ValueError, match="latent_dim must be 2"):
        LatentDistributionSpec("gaussian", None, latent_dim=3)


def test_to_source_spec_contains_distribution_projection():
    payload = LatentDistributionSpec.student_t(df=3).to_source_spec()

    assert payload == {
        "family": "student_t",
        "shape_parameter": 3.0,
        "latent_dim": 2,
        "report_label": "student_t(df=3)",
        "coverage_key": "student_t:3",
    }
