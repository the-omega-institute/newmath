"""Theorem-bound quality projection for lab-local evidence envelopes."""

from __future__ import annotations

from typing import Mapping
import math

from .ledger import LedgerGap, LedgerRowKey


THEOREM_BOUND_ROW = LedgerRowKey("verification", "theorem3-bound-margin")
_REQUIRED_BOUND_KEYS = (
    "theorem3_bound",
    "actual_recovery_error",
    "bound_margin",
    "normalized_gap_d",
    "whitening_deviation_epsilon",
)
_EPS = 1.0e-12


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _finite(value: object) -> float | None:
    if not isinstance(value, (int, float)):
        return None
    scalar = float(value)
    return scalar if math.isfinite(scalar) else None


def _bound_values(metrics: Mapping[str, float]) -> dict[str, float] | None:
    values: dict[str, float] = {}
    for key in _REQUIRED_BOUND_KEYS:
        value = _finite(metrics.get(key))
        if value is None:
            return None
        values[key] = value
    if (
        values["theorem3_bound"] < 0.0
        or values["actual_recovery_error"] < 0.0
        or values["normalized_gap_d"] < 0.0
        or values["whitening_deviation_epsilon"] < 0.0
    ):
        return None
    return values


def _quality_cost(classifier_spec: Mapping[str, object]) -> float:
    output_dim = classifier_spec.get("output_dim", 1)
    if not isinstance(output_dim, (int, float)):
        output_dim = 1
    training = str(classifier_spec.get("training", "")).lower()
    training_cost = 0.04 if "align" in training else 0.01
    dimension_cost = min(0.08, 0.01 * max(1.0, float(output_dim)))
    return float(training_cost + dimension_cost)


def theorem_bound_certificate(
    metrics: Mapping[str, float],
    *,
    max_recovery_error: float = 1.0,
) -> dict[str, object]:
    values = _bound_values(metrics)
    raw_bound = _finite(metrics.get("theorem3_bound"))
    raw_margin = _finite(metrics.get("bound_margin"))
    threshold = {
        "theorem3_bound": 0.0 if raw_bound is None else raw_bound,
        "max_recovery_error": float(max_recovery_error),
    }
    if values is None or not math.isfinite(float(max_recovery_error)) or max_recovery_error <= 0.0:
        return {
            "cert_method": "theorem3-bound-margin",
            "cert_status": "not-certified",
            "cert_score": 0.0,
            "cert_bound": 0.0,
            "cert_actual_recovery_error": 0.0,
            "cert_bound_margin": 0.0 if raw_margin is None else raw_margin,
            "cert_threshold": threshold,
            "cert_reason": "missing or non-finite theorem-bound metric",
        }

    margin = values["bound_margin"]
    certified = margin > 0.0
    scale = max(_EPS, float(max_recovery_error), abs(values["theorem3_bound"]))
    score = _clamp01(margin / scale) if certified else 0.0
    return {
        "cert_method": "theorem3-bound-margin",
        "cert_status": "certified" if certified else "not-certified",
        "cert_score": score,
        "cert_bound": values["theorem3_bound"],
        "cert_actual_recovery_error": values["actual_recovery_error"],
        "cert_bound_margin": margin,
        "cert_threshold": threshold,
        "cert_reason": "positive theorem3 bound margin" if certified else "non-positive theorem3 bound margin",
    }


def theorem_bound_quality_components(
    metrics: Mapping[str, float],
    debt_total: float,
    classifier_spec: Mapping[str, object],
) -> dict[str, float]:
    values = _bound_values(metrics)
    quality_cost = _quality_cost(classifier_spec)
    quality_debt = _clamp01(debt_total)
    if values is None:
        theorem_bound_benefit = 0.0
        gap_penalty = 1.0
        whitening_penalty = 1.0
        recovery_pressure = 1.0
    else:
        scale = max(_EPS, 1.0, abs(values["theorem3_bound"]))
        recovery_pressure = _clamp01(values["actual_recovery_error"] / scale)
        margin_score = _clamp01(values["bound_margin"] / scale)
        gap_penalty = _clamp01(values["normalized_gap_d"])
        whitening_penalty = _clamp01(values["whitening_deviation_epsilon"])
        theorem_bound_benefit = _clamp01(
            margin_score - 0.25 * gap_penalty - 0.25 * whitening_penalty
        )
        if classifier_spec.get("cert_status") != "certified":
            theorem_bound_benefit = 0.0

    quality_q = theorem_bound_benefit - quality_cost - quality_debt
    quality_threshold = 0.0
    return {
        "theorem_bound_benefit": theorem_bound_benefit,
        "theorem_bound_gap_penalty": gap_penalty,
        "theorem_bound_whitening_penalty": whitening_penalty,
        "theorem_bound_recovery_pressure": recovery_pressure,
        "quality_benefit": theorem_bound_benefit,
        "quality_cost": quality_cost,
        "quality_debt": quality_debt,
        "quality_q": quality_q,
        "quality_threshold": quality_threshold,
        "quality_margin": quality_q - quality_threshold,
    }


def theorem_bound_ledger_gap(metrics: Mapping[str, float]) -> LedgerGap | None:
    values = _bound_values(metrics)
    if values is None:
        return LedgerGap(
            kind=THEOREM_BOUND_ROW.kind,
            residue=THEOREM_BOUND_ROW.residue,
            severity="high",
            status="open",
        )
    margin = values["bound_margin"]
    if margin > 0.0:
        return None
    return LedgerGap(
        kind=THEOREM_BOUND_ROW.kind,
        residue=THEOREM_BOUND_ROW.residue,
        severity="medium" if margin == 0.0 else "high",
        status="partial" if margin == 0.0 else "open",
    )
