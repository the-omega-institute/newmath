"""Lab-local empirical identifiability-bound metrics."""

from __future__ import annotations

import numpy as np


_DENOMINATOR_FLOOR = 1.0e-9
_NORM_FLOOR = 1.0e-12


def _as_matrix(values: np.ndarray, name: str) -> np.ndarray:
    arr = np.asarray(values, dtype=np.float64)
    if arr.ndim != 2:
        raise ValueError(f"{name} must be a matrix")
    if arr.shape[0] < 2 or arr.shape[1] < 1:
        raise ValueError(f"{name} must have at least two rows and one column")
    if not np.all(np.isfinite(arr)):
        raise ValueError(f"{name} must contain only finite values")
    return arr


def _same_shape(left: np.ndarray, right: np.ndarray, left_name: str, right_name: str) -> None:
    if left.shape != right.shape:
        raise ValueError(f"{left_name} and {right_name} must have the same shape")


def _finite_scalar(value: float, name: str) -> float:
    scalar = float(value)
    if not np.isfinite(scalar):
        raise ValueError(f"{name} must be finite")
    return scalar


def _rho_denominator(rho: float) -> float:
    value = _finite_scalar(rho, "rho")
    if not 0.0 < value < 1.0:
        raise ValueError("rho must be strictly between 0 and 1")
    denominator = 2.0 * value * (1.0 - value)
    if denominator < _DENOMINATOR_FLOOR:
        raise ValueError("rho makes the normalized gap denominator unstable")
    return denominator


def _center(values: np.ndarray) -> np.ndarray:
    return values - np.mean(values, axis=0, keepdims=True)


def procrustes_q(h: np.ndarray, z: np.ndarray) -> np.ndarray:
    h_matrix = _as_matrix(h, "h")
    z_matrix = _as_matrix(z, "z")
    _same_shape(h_matrix, z_matrix, "h", "z")
    left = _center(h_matrix)
    right = _center(z_matrix)
    u, _, vt = np.linalg.svd(left.T @ right, full_matrices=False)
    q = u @ vt
    if not np.all(np.isfinite(q)):
        raise ValueError("procrustes solution must be finite")
    return q.astype(np.float64)


def orthogonal_recovery_error(h: np.ndarray, z: np.ndarray) -> float:
    h_matrix = _as_matrix(h, "h")
    z_matrix = _as_matrix(z, "z")
    _same_shape(h_matrix, z_matrix, "h", "z")
    q = procrustes_q(h_matrix, z_matrix)
    residual = _center(h_matrix) @ q - _center(z_matrix)
    scale = max(_NORM_FLOOR, float(np.linalg.norm(_center(z_matrix), ord="fro")))
    return float(np.linalg.norm(residual, ord="fro") / scale)


def empirical_alignment_loss(h: np.ndarray, h_pair: np.ndarray) -> float:
    h_matrix = _as_matrix(h, "h")
    pair_matrix = _as_matrix(h_pair, "h_pair")
    _same_shape(h_matrix, pair_matrix, "h", "h_pair")
    diff = h_matrix - pair_matrix
    return float(np.mean(np.sum(diff * diff, axis=1)) / float(h_matrix.shape[1]))


def whitening_deviation_epsilon(h: np.ndarray) -> float:
    h_matrix = _as_matrix(h, "h")
    centered = _center(h_matrix)
    cov = centered.T @ centered / float(h_matrix.shape[0] - 1)
    target = np.eye(h_matrix.shape[1], dtype=np.float64)
    return float(np.linalg.norm(cov - target, ord="fro"))


def alignment_gap_delta(alignment_loss: float, rho: float) -> float:
    loss = _finite_scalar(alignment_loss, "alignment_loss")
    _rho_denominator(rho)
    if loss < 0.0:
        raise ValueError("alignment_loss must be non-negative")
    return float(max(0.0, loss - 2.0 * (1.0 - float(rho))))


def normalized_gap_d(delta: float, rho: float) -> float:
    gap = _finite_scalar(delta, "delta")
    if gap < 0.0:
        raise ValueError("delta must be non-negative")
    return float(gap / _rho_denominator(rho))


def theorem3_bound(d: float, epsilon: float) -> float:
    normalized_gap = _finite_scalar(d, "d")
    deviation = _finite_scalar(epsilon, "epsilon")
    if normalized_gap < 0.0 or deviation < 0.0:
        raise ValueError("d and epsilon must be non-negative")
    return float(normalized_gap + (deviation + normalized_gap) ** 2)


def bound_margin(bound: float, actual_recovery_error: float) -> float:
    upper = _finite_scalar(bound, "bound")
    actual = _finite_scalar(actual_recovery_error, "actual_recovery_error")
    return float(upper - actual)


def identifiability_bound_metrics(
    h: np.ndarray,
    h_pair: np.ndarray,
    z: np.ndarray,
    rho: float,
) -> dict[str, float]:
    alignment_loss = empirical_alignment_loss(h, h_pair)
    delta = alignment_gap_delta(alignment_loss, rho)
    epsilon = whitening_deviation_epsilon(h)
    d_value = normalized_gap_d(delta, rho)
    bound = theorem3_bound(d_value, epsilon)
    actual = orthogonal_recovery_error(h, z)
    return {
        "alignment_loss": alignment_loss,
        "alignment_gap_delta": delta,
        "whitening_deviation_epsilon": epsilon,
        "normalized_gap_d": d_value,
        "theorem3_bound": bound,
        "actual_recovery_error": actual,
        "bound_margin": bound_margin(bound, actual),
    }
