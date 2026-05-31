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


def classifier_certificate(
    metrics: dict[str, float],
    *,
    min_r2: float = 0.85,
    min_proxy: float = 0.70,
) -> dict[str, object]:
    cert_r2 = float(metrics.get("linear_identifiability_r2", 0.0))
    cert_proxy = float(metrics.get("approx_identifiability_proxy", 0.0))
    cert_score = min(cert_r2 / min_r2, cert_proxy / min_proxy) if min_r2 > 0.0 and min_proxy > 0.0 else 0.0
    certified = cert_r2 >= min_r2 and cert_proxy >= min_proxy
    cert_threshold = {
        "linear_identifiability_r2": float(min_r2),
        "approx_identifiability_proxy": float(min_proxy),
    }
    cert_reason = (
        "linear_identifiability_r2 and approx_identifiability_proxy meet thresholds"
        if certified
        else "linear_identifiability_r2 or approx_identifiability_proxy below threshold"
    )
    return {
        "cert_method": "inline-threshold",
        "cert_status": "certified" if certified else "uncertified",
        "cert_score": float(max(0.0, cert_score)),
        "cert_r2": cert_r2,
        "cert_proxy": cert_proxy,
        "cert_threshold": cert_threshold,
        "cert_reason": cert_reason,
    }


def quality_components(
    metrics: dict[str, float],
    debt_total: float,
    classifier_spec: dict[str, object],
) -> dict[str, float]:
    r2 = float(metrics.get("linear_identifiability_r2", 0.0))
    proxy = float(metrics.get("approx_identifiability_proxy", 0.0))
    quality_benefit = max(0.0, min(1.0, 0.5 * r2 + 0.5 * proxy))
    if classifier_spec.get("cert_status") != "certified":
        quality_benefit = 0.0

    output_dim = classifier_spec.get("output_dim", 1)
    if not isinstance(output_dim, (int, float)):
        output_dim = 1
    training = str(classifier_spec.get("training", "")).lower()
    training_cost = 0.04 if "align" in training else 0.01
    dimension_cost = min(0.08, 0.01 * max(1.0, float(output_dim)))
    quality_cost = training_cost + dimension_cost

    quality_debt = max(0.0, min(1.0, float(debt_total)))
    quality_q = quality_benefit - quality_cost - quality_debt
    quality_threshold = 0.0
    return {
        "quality_benefit": quality_benefit,
        "quality_cost": quality_cost,
        "quality_debt": quality_debt,
        "quality_q": quality_q,
        "quality_threshold": quality_threshold,
        "quality_margin": quality_q - quality_threshold,
    }
