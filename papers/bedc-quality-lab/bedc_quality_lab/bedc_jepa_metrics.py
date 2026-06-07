"""Metrics for distinction and gap-ledger world-model claims."""

from __future__ import annotations

import numpy as np


def binary_accuracy(scores: np.ndarray, labels: np.ndarray, *, threshold: float = 0.5) -> float:
    score_arr = np.asarray(scores, dtype=np.float64)
    label_arr = np.asarray(labels, dtype=bool)
    if score_arr.shape != label_arr.shape:
        raise ValueError("scores and labels must have the same shape")
    return float(np.mean((score_arr >= threshold) == label_arr))


def masked_binary_accuracy(
    scores: np.ndarray,
    labels: np.ndarray,
    mask: np.ndarray,
    *,
    threshold: float = 0.5,
) -> float:
    score_arr = np.asarray(scores, dtype=np.float64)
    label_arr = np.asarray(labels, dtype=bool)
    mask_arr = np.asarray(mask, dtype=bool)
    if score_arr.shape != label_arr.shape or score_arr.shape != mask_arr.shape:
        raise ValueError("scores, labels, and mask must have the same shape")
    if not np.any(mask_arr):
        return 1.0
    return float(np.mean((score_arr[mask_arr] >= threshold) == label_arr[mask_arr]))


def false_claim_rate(
    claim_scores: np.ndarray,
    claim_labels: np.ndarray,
    gap_labels: np.ndarray,
    *,
    claim_threshold: float = 0.5,
    confidence_margin: float = 0.25,
) -> float:
    """Rate of confident distinction claims inside gap-labeled cases."""
    scores = np.asarray(claim_scores, dtype=np.float64)
    labels = np.asarray(claim_labels, dtype=bool)
    gaps = np.asarray(gap_labels, dtype=bool)
    if scores.shape != labels.shape or scores.shape != gaps.shape:
        raise ValueError("claim scores, labels, and gaps must have the same shape")
    if not np.any(gaps):
        return 0.0
    confident = np.abs(scores - claim_threshold) >= confidence_margin
    wrong = (scores >= claim_threshold) != labels
    return float(np.mean(confident[gaps] & wrong[gaps]))


def gap_detection_auc(gap_scores: np.ndarray, gap_labels: np.ndarray) -> float:
    """Compute a small dependency-free AUROC for gap detection."""
    scores = np.asarray(gap_scores, dtype=np.float64)
    labels = np.asarray(gap_labels, dtype=bool)
    if scores.shape != labels.shape:
        raise ValueError("gap_scores and gap_labels must have the same shape")
    positives = scores[labels]
    negatives = scores[~labels]
    if positives.size == 0 or negatives.size == 0:
        return 1.0
    greater = positives[:, None] > negatives[None, :]
    equal = positives[:, None] == negatives[None, :]
    return float(np.mean(greater) + 0.5 * np.mean(equal))


def unlogged_error_rate(
    claim_scores: np.ndarray,
    claim_labels: np.ndarray,
    gap_scores: np.ndarray,
    *,
    claim_threshold: float = 0.5,
    gap_threshold: float = 0.5,
) -> float:
    """Errors whose gap head does not activate."""
    scores = np.asarray(claim_scores, dtype=np.float64)
    labels = np.asarray(claim_labels, dtype=bool)
    gaps = np.asarray(gap_scores, dtype=np.float64)
    if scores.shape != labels.shape or scores.shape != gaps.shape:
        raise ValueError("claim scores, labels, and gap scores must have the same shape")
    errors = (scores >= claim_threshold) != labels
    unlogged = gaps < gap_threshold
    return float(np.mean(errors & unlogged))


def certified_coverage(gap_scores: np.ndarray, *, gap_threshold: float = 0.5) -> float:
    gaps = np.asarray(gap_scores, dtype=np.float64)
    return float(np.mean(gaps < gap_threshold))


def bedc_debt_score(
    *,
    unlogged_error: float,
    false_claim: float,
    gap_auc: float,
    certified: float,
) -> float:
    """Small scope-relative debt score for the boundary-gated toy world."""
    raw = 0.40 * unlogged_error + 0.30 * false_claim + 0.20 * (1.0 - gap_auc) + 0.10 * (1.0 - certified)
    return float(max(0.0, min(1.0, raw)))
