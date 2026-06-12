"""Package-local latent distribution specifications for source sweeps."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from math import gamma
from typing import Any

import numpy as np


_SUPPORTED_FAMILIES = frozenset(
    {
        "gaussian",
        "laplace",
        "uniform",
        "student_t",
        "generalized_normal",
    }
)
_GENERALIZED_NORMAL_ALPHA_VALUES = (0.5, 1.0, 2.0, 4.0, 8.0)
_EPS = 1.0e-12


@dataclass(frozen=True)
class LatentDistributionSpec:
    family: str
    shape_parameter: float | None
    latent_dim: int = 2

    def __post_init__(self) -> None:
        if self.latent_dim != 2:
            raise ValueError("latent_dim must be 2")
        if self.family not in _SUPPORTED_FAMILIES:
            raise ValueError(f"unknown latent distribution family: {self.family!r}")
        shape = self.shape_parameter
        if self.family in {"gaussian", "laplace", "uniform"}:
            if shape is not None:
                raise ValueError(f"{self.family} latent distribution does not accept a shape parameter")
            return
        if not isinstance(shape, (int, float)) or not np.isfinite(float(shape)) or float(shape) <= 0.0:
            raise ValueError(f"{self.family} latent distribution requires a positive finite shape parameter")
        object.__setattr__(self, "shape_parameter", float(shape))

    @classmethod
    def gaussian(cls) -> "LatentDistributionSpec":
        return cls("gaussian", None)

    @classmethod
    def laplace(cls) -> "LatentDistributionSpec":
        return cls("laplace", None)

    @classmethod
    def uniform(cls) -> "LatentDistributionSpec":
        return cls("uniform", None)

    @classmethod
    def student_t(cls, df: float = 3) -> "LatentDistributionSpec":
        if float(df) <= 2.0:
            raise ValueError("student_t df must be greater than 2")
        return cls("student_t", float(df))

    @classmethod
    def generalized_normal(cls, alpha: float) -> "LatentDistributionSpec":
        if float(alpha) <= 0.0:
            raise ValueError("generalized_normal alpha must be positive")
        return cls("generalized_normal", float(alpha))

    def sample(self, n: int, seed: int) -> np.ndarray:
        if not isinstance(n, int) or n < 2:
            raise ValueError("n must be an integer at least 2")
        rng = np.random.default_rng(seed)
        if self.family == "gaussian":
            raw = rng.normal(size=(n, self.latent_dim))
        elif self.family == "laplace":
            raw = rng.laplace(size=(n, self.latent_dim))
        elif self.family == "uniform":
            raw = rng.uniform(-1.0, 1.0, size=(n, self.latent_dim))
        elif self.family == "student_t":
            raw = rng.standard_t(df=float(self.shape_parameter), size=(n, self.latent_dim))
        elif self.family == "generalized_normal":
            raw = _sample_generalized_normal(rng, n, self.latent_dim, float(self.shape_parameter))
        else:  # pragma: no cover - guarded by __post_init__
            raise ValueError(f"unknown latent distribution family: {self.family!r}")
        return _center_and_normalize(raw)

    def distribution_family_key(self) -> str:
        if self.shape_parameter is None:
            return self.family
        value = _shape_label(float(self.shape_parameter))
        return f"{self.family}:{value}"

    def report_label(self) -> str:
        if self.shape_parameter is None:
            return self.family
        return f"{self.family}({self._shape_name()}={_shape_label(float(self.shape_parameter))})"

    def to_source_spec(self) -> dict[str, object]:
        return {
            "family": self.family,
            "shape_parameter": self.shape_parameter,
            "latent_dim": self.latent_dim,
            "report_label": self.report_label(),
            "coverage_key": self.distribution_family_key(),
        }

    def _shape_name(self) -> str:
        if self.family == "student_t":
            return "df"
        if self.family == "generalized_normal":
            return "alpha"
        return "shape"


def _shape_label(value: float) -> str:
    if float(value).is_integer():
        return str(int(value))
    return f"{value:g}"


def _center_and_normalize(values: np.ndarray) -> np.ndarray:
    array = np.asarray(values, dtype=np.float64)
    if array.ndim != 2 or array.shape[1] != 2:
        raise ValueError("latent samples must have shape (n, 2)")
    if not np.all(np.isfinite(array)):
        raise ValueError("latent samples must be finite")
    centered = array - np.mean(array, axis=0, keepdims=True)
    scale = np.std(centered, axis=0, keepdims=True)
    if np.any(scale <= _EPS):
        raise ValueError("latent samples must have positive variance")
    normalized = centered / scale
    if not np.all(np.isfinite(normalized)):
        raise ValueError("normalized latent samples must be finite")
    return normalized.astype(np.float64)


def _sample_generalized_normal(rng: np.random.Generator, n: int, latent_dim: int, alpha: float) -> np.ndarray:
    magnitude = rng.gamma(shape=1.0 / alpha, scale=1.0, size=(n, latent_dim)) ** (1.0 / alpha)
    signs = rng.choice(np.array([-1.0, 1.0], dtype=np.float64), size=(n, latent_dim))
    variance = gamma(3.0 / alpha) / gamma(1.0 / alpha)
    return signs * magnitude / np.sqrt(variance)


def _iter_coverage_values(values: Any) -> Iterable[str]:
    if isinstance(values, str):
        yield values
        return
    if isinstance(values, LatentDistributionSpec):
        yield values.distribution_family_key()
        return
    if isinstance(values, dict):
        coverage = values.get("coverage_key")
        if isinstance(coverage, str):
            yield coverage
            return
        family = values.get("family")
        shape = values.get("shape_parameter")
        if isinstance(family, str):
            if shape is None:
                yield family
            elif isinstance(shape, (int, float)):
                yield f"{family}:{_shape_label(float(shape))}"
            return
    if isinstance(values, Iterable):
        for value in values:
            yield from _iter_coverage_values(value)


def covered_distribution_family_keys(source_spec: Any) -> tuple[str, ...]:
    if isinstance(source_spec, dict):
        values = [
            source_spec.get("latent_distribution"),
            source_spec.get("latent_distribution_coverage_keys"),
        ]
    else:
        values = source_spec
    observed = set(_iter_coverage_values(values))
    return tuple(key for key in CANONICAL_LATENT_DISTRIBUTION_KEYS if key in observed)


CANONICAL_LATENT_DISTRIBUTION_ARMS = (
    LatentDistributionSpec.gaussian(),
    LatentDistributionSpec.laplace(),
    LatentDistributionSpec.uniform(),
    LatentDistributionSpec.student_t(df=3),
    LatentDistributionSpec.generalized_normal(alpha=0.5),
    LatentDistributionSpec.generalized_normal(alpha=1),
    LatentDistributionSpec.generalized_normal(alpha=2),
    LatentDistributionSpec.generalized_normal(alpha=4),
    LatentDistributionSpec.generalized_normal(alpha=8),
)
CANONICAL_LATENT_DISTRIBUTION_KEYS = tuple(
    spec.distribution_family_key()
    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS
)
