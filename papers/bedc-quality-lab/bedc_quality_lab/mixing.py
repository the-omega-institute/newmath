"""Canonical nonlinear mixing families for the quality lab."""

from __future__ import annotations

from collections.abc import Iterable
from typing import Any

import numpy as np


CANONICAL_MIXING_FAMILIES = (
    "spiral",
    "sinusoidal_shear",
    "parabolic_shear",
    "realnvp_coupling",
)
DEFAULT_MIXING = "sinusoidal_shear"


def _as_latent_matrix(z: np.ndarray) -> np.ndarray:
    array = np.asarray(z, dtype=np.float64)
    if array.ndim != 2 or array.shape[1] != 2:
        raise ValueError("z must have shape (n, 2)")
    return array


def _spiral(z: np.ndarray) -> np.ndarray:
    radius = np.sqrt(np.sum(np.square(z), axis=1))
    theta = 0.42 * radius
    cos_theta = np.cos(theta)
    sin_theta = np.sin(theta)
    x0 = cos_theta * z[:, 0] - sin_theta * z[:, 1]
    x1 = sin_theta * z[:, 0] + cos_theta * z[:, 1]
    return np.column_stack([x0, x1])


def _sinusoidal_shear(z: np.ndarray) -> np.ndarray:
    x0 = z[:, 0] + 0.35 * np.sin(1.7 * z[:, 1])
    x1 = z[:, 1] + 0.25 * np.square(z[:, 0]) - 0.25
    return np.column_stack([x0, x1])


def _parabolic_shear(z: np.ndarray) -> np.ndarray:
    x0 = z[:, 0]
    x1 = z[:, 1] + 0.25 * np.square(z[:, 0]) - 0.25
    return np.column_stack([x0, x1])


def _realnvp_coupling(z: np.ndarray) -> np.ndarray:
    scale = np.exp(0.18 * np.tanh(z[:, 0]))
    shift = 0.30 * np.sin(1.3 * z[:, 0])
    x0 = z[:, 0]
    x1 = scale * z[:, 1] + shift
    return np.column_stack([x0, x1])


_MIXERS = {
    "spiral": _spiral,
    "sinusoidal_shear": _sinusoidal_shear,
    "parabolic_shear": _parabolic_shear,
    "realnvp_coupling": _realnvp_coupling,
}


def canonical_mixing_families() -> tuple[str, ...]:
    return CANONICAL_MIXING_FAMILIES


def mix_latents(z: np.ndarray, mixing: str = DEFAULT_MIXING) -> np.ndarray:
    array = _as_latent_matrix(z)
    try:
        mixed = _MIXERS[mixing](array)
    except KeyError as exc:
        raise ValueError(f"unknown mixing family: {mixing!r}") from exc
    return np.asarray(mixed, dtype=np.float64)


def _iter_mixing_values(values: Any) -> Iterable[str]:
    if isinstance(values, str):
        yield values
        return
    if isinstance(values, Iterable):
        for value in values:
            if isinstance(value, str):
                yield value


def covered_canonical_mixing_families(values: Any) -> tuple[str, ...]:
    observed = set(_iter_mixing_values(values))
    return tuple(name for name in CANONICAL_MIXING_FAMILIES if name in observed)
