"""Metrics for the Gaussian-OU representation experiment."""

from __future__ import annotations

import numpy as np


def _as_matrix(values: np.ndarray, name: str) -> np.ndarray:
    arr = np.asarray(values, dtype=np.float64)
    if arr.ndim != 2:
        raise ValueError(f"{name} must be a matrix")
    return arr


def linear_identifiability_r2(h: np.ndarray, z: np.ndarray) -> float:
    h = _as_matrix(h, "h")
    z = _as_matrix(z, "z")
    if h.shape[0] != z.shape[0]:
        raise ValueError("h and z must have the same row count")
    design = np.column_stack([h, np.ones(h.shape[0])])
    coef, *_ = np.linalg.lstsq(design, z, rcond=None)
    pred = design @ coef
    ss_res = float(np.sum((z - pred) ** 2))
    ss_tot = float(np.sum((z - np.mean(z, axis=0, keepdims=True)) ** 2))
    if ss_tot <= 0.0:
        return 1.0 if ss_res <= 1e-12 else 0.0
    return max(0.0, min(1.0, 1.0 - ss_res / ss_tot))


def orthogonality_error(h: np.ndarray) -> float:
    h = _as_matrix(h, "h")
    centered = h - np.mean(h, axis=0, keepdims=True)
    scale = np.sqrt(np.sum(centered * centered, axis=0, keepdims=True))
    scale = np.where(scale <= 1e-12, 1.0, scale)
    normalized = centered / scale
    gram = normalized.T @ normalized
    off_diag = gram - np.diag(np.diag(gram))
    return float(np.linalg.norm(off_diag, ord="fro"))


def covariance_deviation(h: np.ndarray) -> float:
    h = _as_matrix(h, "h")
    centered = h - np.mean(h, axis=0, keepdims=True)
    cov = centered.T @ centered / max(1, h.shape[0] - 1)
    target = np.eye(h.shape[1])
    return float(np.linalg.norm(cov - target, ord="fro"))


def approximate_identifiability_proxy(h: np.ndarray, z: np.ndarray) -> float:
    r2 = linear_identifiability_r2(h, z)
    ortho_penalty = min(1.0, orthogonality_error(h))
    cov_penalty = min(1.0, covariance_deviation(h) / max(1.0, h.shape[1]))
    return float(max(0.0, r2 - 0.25 * ortho_penalty - 0.25 * cov_penalty))


def metric_bundle(h: np.ndarray, z: np.ndarray) -> dict[str, float]:
    return {
        "linear_identifiability_r2": linear_identifiability_r2(h, z),
        "orthogonality_error": orthogonality_error(h),
        "covariance_deviation": covariance_deviation(h),
        "approx_identifiability_proxy": approximate_identifiability_proxy(h, z),
    }
