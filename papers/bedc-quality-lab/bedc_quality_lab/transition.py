"""OU transition-kernel source surface for the quality lab."""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Any

import numpy as np


_ISOTROPY_TOLERANCE = 1.0e-12


def _rho_tuple(values: tuple[float, ...]) -> tuple[float, ...]:
    if not values:
        raise ValueError("rho_by_axis must be non-empty")
    rho = tuple(float(value) for value in values)
    if not all(math.isfinite(value) for value in rho):
        raise ValueError("rho_by_axis values must be finite")
    if not all(-1.0 < value < 1.0 for value in rho):
        raise ValueError("rho_by_axis values must be strictly between -1 and 1")
    return rho


@dataclass(frozen=True)
class TransitionKernelSpec:
    family: str = "ornstein-uhlenbeck"
    rho_by_axis: tuple[float, ...] = (0.82, 0.82)
    noise_family: str = "gaussian"

    def __post_init__(self) -> None:
        if self.family != "ornstein-uhlenbeck":
            raise ValueError("transition family must be ornstein-uhlenbeck")
        if self.noise_family != "gaussian":
            raise ValueError("transition noise_family must be gaussian")
        object.__setattr__(self, "rho_by_axis", _rho_tuple(tuple(self.rho_by_axis)))

    @classmethod
    def isotropic(cls, rho: float, *, latent_dim: int) -> "TransitionKernelSpec":
        if latent_dim <= 0:
            raise ValueError("latent_dim must be positive")
        return cls(rho_by_axis=tuple(float(rho) for _ in range(latent_dim)))

    def is_isotropic(self, tolerance: float = _ISOTROPY_TOLERANCE) -> bool:
        if tolerance < 0.0 or not math.isfinite(float(tolerance)):
            raise ValueError("tolerance must be finite and non-negative")
        first = self.rho_by_axis[0]
        return all(abs(value - first) <= tolerance for value in self.rho_by_axis)

    def anisotropy_gap(self) -> float:
        return float(max(self.rho_by_axis) - min(self.rho_by_axis))

    def eigenvalue_interleaving_summary(self) -> dict[str, Any]:
        sorted_values = tuple(sorted(self.rho_by_axis, reverse=True))
        gaps = tuple(abs(sorted_values[index] - sorted_values[index + 1]) for index in range(len(sorted_values) - 1))
        return {
            "operator": "diagonal-ou-transition",
            "eigenvalues": list(self.rho_by_axis),
            "sorted_eigenvalues": list(sorted_values),
            "adjacent_gaps": list(gaps),
            "min_adjacent_gap": float(min(gaps)) if gaps else 0.0,
            "anisotropy_gap": self.anisotropy_gap(),
            "boundary": "Gaussian latent + anisotropic transition; transition noise is Gaussian.",
        }

    def to_source_spec(self) -> dict[str, Any]:
        return {
            "family": self.family,
            "rho_by_axis": list(self.rho_by_axis),
            "noise_family": self.noise_family,
            "isotropic": self.is_isotropic(),
            "anisotropy_gap": self.anisotropy_gap(),
            "eigenvalue_interleaving": self.eigenvalue_interleaving_summary(),
        }


def make_transition_pair(z: np.ndarray, spec: TransitionKernelSpec, seed: int) -> np.ndarray:
    values = np.asarray(z, dtype=np.float64)
    if values.ndim != 2:
        raise ValueError("z must be a matrix")
    if values.shape[1] != len(spec.rho_by_axis):
        raise ValueError("z column count must match transition rho_by_axis length")
    if not np.all(np.isfinite(values)):
        raise ValueError("z must contain only finite values")
    rho = np.asarray(spec.rho_by_axis, dtype=np.float64)
    rng = np.random.default_rng(seed)
    eta = rng.normal(size=values.shape)
    scale = np.sqrt(1.0 - rho * rho)
    return (values * rho + eta * scale).astype(np.float64)
