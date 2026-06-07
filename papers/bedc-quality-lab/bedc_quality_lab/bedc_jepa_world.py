"""Boundary-gated toy worlds for BEDC-JEPA experiments."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from bedc_quality_lab.toy_world import make_latents, make_ou_pair, mix_latents


@dataclass(frozen=True)
class BoundaryGatedBatch:
    z: np.ndarray
    z_pair: np.ndarray
    x: np.ndarray
    x_pair: np.ndarray
    distinction: np.ndarray
    distinction_pair: np.ndarray
    gap: np.ndarray
    gap_pair: np.ndarray
    radius: float
    gap_width: float


def _radius_squared(z: np.ndarray) -> np.ndarray:
    if z.ndim != 2 or z.shape[1] != 2:
        raise ValueError("z must have shape (n, 2)")
    return np.sum(z * z, axis=1)


def boundary_distinction(z: np.ndarray, *, radius: float) -> np.ndarray:
    """Return the inside/outside operational distinction."""
    return _radius_squared(z) <= radius * radius


def boundary_gap(z: np.ndarray, *, radius: float, gap_width: float) -> np.ndarray:
    """Return cases whose distinction claim is too near the boundary."""
    if gap_width <= 0.0:
        raise ValueError("gap_width must be positive")
    distance_to_boundary = np.abs(_radius_squared(z) - radius * radius)
    return distance_to_boundary <= gap_width


def make_boundary_gated_batch(
    n: int,
    *,
    rho: float = 0.82,
    radius: float = 1.0,
    gap_width: float = 0.12,
    seed: int = 31,
) -> BoundaryGatedBatch:
    """Create a small world with continuous state, distinction, and gap labels."""
    z = make_latents(n, seed=seed)
    z_pair = make_ou_pair(z, rho=rho, seed=seed + 1)
    distinction = boundary_distinction(z, radius=radius)
    distinction_pair = boundary_distinction(z_pair, radius=radius)
    gap = boundary_gap(z, radius=radius, gap_width=gap_width)
    gap_pair = boundary_gap(z_pair, radius=radius, gap_width=gap_width)
    return BoundaryGatedBatch(
        z=z,
        z_pair=z_pair,
        x=mix_latents(z),
        x_pair=mix_latents(z_pair),
        distinction=distinction,
        distinction_pair=distinction_pair,
        gap=gap,
        gap_pair=gap_pair,
        radius=radius,
        gap_width=gap_width,
    )


def standardize_observation(x: np.ndarray) -> np.ndarray:
    """Deterministic representation used by no-torch calibration runs."""
    centered = x - np.mean(x, axis=0, keepdims=True)
    scale = np.std(centered, axis=0, keepdims=True)
    scale = np.where(scale <= 1e-12, 1.0, scale)
    return centered / scale


def radial_distinction_score(h: np.ndarray, *, radius: float) -> np.ndarray:
    """Score inside-boundary claims from a representation radius."""
    if h.ndim != 2 or h.shape[1] != 2:
        raise ValueError("h must have shape (n, 2)")
    margin = radius * radius - np.sum(h * h, axis=1)
    return 1.0 / (1.0 + np.exp(-4.0 * margin))


def radial_gap_score(h: np.ndarray, *, radius: float, gap_width: float) -> np.ndarray:
    """Score whether the representation is near the operational boundary."""
    if h.ndim != 2 or h.shape[1] != 2:
        raise ValueError("h must have shape (n, 2)")
    if gap_width <= 0.0:
        raise ValueError("gap_width must be positive")
    distance_to_boundary = np.abs(np.sum(h * h, axis=1) - radius * radius)
    margin = gap_width - distance_to_boundary
    return 1.0 / (1.0 + np.exp(-18.0 * margin))
