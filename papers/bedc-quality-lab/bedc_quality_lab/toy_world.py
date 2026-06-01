"""Deterministic Gaussian-OU toy world."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .transition import TransitionKernelSpec, make_transition_pair


@dataclass(frozen=True)
class ToyBatch:
    z: np.ndarray
    z_pair: np.ndarray
    x: np.ndarray
    x_pair: np.ndarray


def make_latents(n: int, *, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    return rng.normal(size=(n, 2)).astype(np.float64)


def make_ou_pair(z: np.ndarray, *, rho: float, seed: int) -> np.ndarray:
    if z.ndim != 2 or z.shape[1] != 2:
        raise ValueError("z must have shape (n, 2)")
    spec = TransitionKernelSpec.isotropic(rho, latent_dim=z.shape[1])
    return make_transition_pair(z, spec, seed)


def mix_latents(z: np.ndarray) -> np.ndarray:
    if z.ndim != 2 or z.shape[1] != 2:
        raise ValueError("z must have shape (n, 2)")
    x0 = z[:, 0] + 0.35 * np.sin(1.7 * z[:, 1])
    x1 = z[:, 1] + 0.25 * np.square(z[:, 0]) - 0.25
    return np.column_stack([x0, x1]).astype(np.float64)


def make_toy_batch(
    n: int,
    *,
    rho: float = 0.82,
    seed: int = 17,
    transition_kernel: TransitionKernelSpec | None = None,
) -> ToyBatch:
    z = make_latents(n, seed=seed)
    spec = transition_kernel if transition_kernel is not None else TransitionKernelSpec.isotropic(rho, latent_dim=z.shape[1])
    z_pair = make_transition_pair(z, spec, seed + 1)
    return ToyBatch(z=z, z_pair=z_pair, x=mix_latents(z), x_pair=mix_latents(z_pair))
