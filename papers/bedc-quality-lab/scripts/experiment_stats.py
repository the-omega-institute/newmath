"""Small statistical helpers for lab experiment scripts."""

from __future__ import annotations

import math
import statistics
from typing import Any, Iterable


def sample_std(values: Iterable[float]) -> float:
    samples = [float(value) for value in values]
    if len(samples) < 2:
        return 0.0
    return float(statistics.stdev(samples))


def metric_stats(values: Iterable[float]) -> dict[str, float | int]:
    samples = [float(value) for value in values]
    n = len(samples)
    if n == 0:
        return {
            "n": 0,
            "mean": math.nan,
            "std": math.nan,
            "ci95_half_width": math.nan,
            "ci95_low": math.nan,
            "ci95_high": math.nan,
        }
    mean = float(statistics.fmean(samples))
    std = sample_std(samples)
    ci95 = 0.0 if n < 2 else float(1.96 * std / math.sqrt(n))
    return {
        "n": n,
        "mean": mean,
        "std": std,
        "ci95_half_width": ci95,
        "ci95_low": mean - ci95,
        "ci95_high": mean + ci95,
    }


def fit_log_log_slope(points: Iterable[dict[str, float | int]]) -> dict[str, Any]:
    usable = [
        (math.log(float(point["sample_count"])), math.log(float(point["std"])))
        for point in points
        if float(point["std"]) > 0.0
    ]
    n = len(usable)
    if n < 3:
        return {
            "status": "insufficient_positive_std",
            "n": n,
            "slope": math.nan,
            "intercept": math.nan,
            "slope_standard_error": math.nan,
            "slope_ci95_low": math.nan,
            "slope_ci95_high": math.nan,
        }

    xs = [point[0] for point in usable]
    ys = [point[1] for point in usable]
    x_mean = statistics.fmean(xs)
    y_mean = statistics.fmean(ys)
    sxx = sum((x - x_mean) ** 2 for x in xs)
    slope = sum((x - x_mean) * (y - y_mean) for x, y in usable) / sxx
    intercept = y_mean - slope * x_mean
    residual_sse = sum((y - (intercept + slope * x)) ** 2 for x, y in usable)
    df = n - 2
    residual_var = residual_sse / df if df > 0 else 0.0
    slope_se = math.sqrt(residual_var / sxx) if sxx > 0.0 else math.nan
    t95_by_df = {1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571}
    t95 = t95_by_df.get(df, 1.96)
    low = slope - t95 * slope_se
    high = slope + t95 * slope_se
    return {
        "status": "ok",
        "n": n,
        "slope": float(slope),
        "intercept": float(intercept),
        "slope_standard_error": float(slope_se),
        "slope_ci95_low": float(low),
        "slope_ci95_high": float(high),
    }


def _finite_interval(fit: dict[str, Any]) -> tuple[float, float] | None:
    if fit.get("status") != "ok":
        return None
    low = float(fit["slope_ci95_low"])
    high = float(fit["slope_ci95_high"])
    if math.isnan(low) or math.isnan(high):
        return None
    return (low, high)


def slope_ci_overlap(left: dict[str, Any], right: dict[str, Any]) -> bool:
    left_interval = _finite_interval(left)
    right_interval = _finite_interval(right)
    if left_interval is None or right_interval is None:
        return False
    return max(left_interval[0], right_interval[0]) <= min(left_interval[1], right_interval[1])


def slope_ci_common_overlap(fits: Iterable[dict[str, Any]]) -> dict[str, Any]:
    intervals = [_finite_interval(fit) for fit in fits]
    finite_intervals = [interval for interval in intervals if interval is not None]
    if len(finite_intervals) != len(intervals) or not finite_intervals:
        return {
            "status": "insufficient_valid_ci",
            "fit_count": len(intervals),
            "valid_fit_count": len(finite_intervals),
            "all_overlap": False,
            "overlap_low": math.nan,
            "overlap_high": math.nan,
        }
    overlap_low = max(interval[0] for interval in finite_intervals)
    overlap_high = min(interval[1] for interval in finite_intervals)
    return {
        "status": "ok",
        "fit_count": len(intervals),
        "valid_fit_count": len(finite_intervals),
        "all_overlap": bool(overlap_low <= overlap_high),
        "overlap_low": float(overlap_low),
        "overlap_high": float(overlap_high),
    }


def all_slope_ci_overlap(fits: Iterable[dict[str, Any]]) -> bool:
    return bool(slope_ci_common_overlap(fits)["all_overlap"])
