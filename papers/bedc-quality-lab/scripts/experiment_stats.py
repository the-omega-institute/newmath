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


def _closed_prefix_row(k: int, n: int, status: str) -> dict[str, float | int | str]:
    return {
        "k": int(k),
        "n": int(n),
        "status": status,
        "mean": math.nan,
        "std": math.nan,
        "ci95_half_width": math.nan,
        "ci95_low": math.nan,
        "ci95_high": math.nan,
    }


def prefix_metric_stats(
    values: Iterable[float],
    ks: Iterable[int],
) -> list[dict[str, float | int | str]]:
    samples = [float(value) for value in values]
    rows: list[dict[str, float | int | str]] = []
    for raw_k in ks:
        k = int(raw_k)
        if k < 2 or len(samples) < k:
            rows.append(_closed_prefix_row(k, min(max(k, 0), len(samples)), "insufficient_points"))
            continue
        prefix = samples[:k]
        if any(not math.isfinite(value) for value in prefix):
            rows.append(_closed_prefix_row(k, k, "non_finite_value"))
            continue
        summary = metric_stats(prefix)
        rows.append(
            {
                "k": k,
                "n": int(summary["n"]),
                "status": "ok",
                "mean": float(summary["mean"]),
                "std": float(summary["std"]),
                "ci95_half_width": float(summary["ci95_half_width"]),
                "ci95_low": float(summary["ci95_low"]),
                "ci95_high": float(summary["ci95_high"]),
            }
        )
    return rows


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


def fit_ci_halfwidth_decay(points: Iterable[dict[str, float | int | str]]) -> dict[str, Any]:
    expected_interval = (-0.8, -0.3)
    usable: list[dict[str, float | int]] = []
    ignored: list[dict[str, Any]] = []
    for point in points:
        k = point.get("k")
        status = str(point.get("status", "ok"))
        try:
            k_value = float(k)
            half_width = float(point["ci95_half_width"])
        except (KeyError, TypeError, ValueError):
            ignored.append({"k": k, "status": "missing_or_invalid_half_width"})
            continue
        if status != "ok":
            ignored.append({"k": int(k_value) if math.isfinite(k_value) else k, "status": status})
            continue
        if not math.isfinite(k_value) or k_value <= 0.0:
            ignored.append({"k": k, "status": "non_positive_or_non_finite_k"})
            continue
        if not math.isfinite(half_width) or half_width <= 0.0:
            ignored.append({"k": int(k_value), "status": "non_positive_or_non_finite_half_width"})
            continue
        usable.append({"sample_count": int(k_value), "std": half_width})

    fit = fit_log_log_slope(usable)
    slope = float(fit["slope"])
    low, high = expected_interval
    return {
        **fit,
        "expected_slope_interval": list(expected_interval),
        "slope_in_expected_interval": bool(fit["status"] == "ok" and low <= slope <= high),
        "usable_points": [
            {"k": int(point["sample_count"]), "ci95_half_width": float(point["std"])}
            for point in usable
        ],
        "ignored_points": ignored,
    }


def estimate_min_k_for_ci(
    points: Iterable[dict[str, float | int | str]],
    *,
    target_ci95_half_width: float,
    decay_fit: dict[str, Any] | None = None,
) -> dict[str, Any]:
    target = float(target_ci95_half_width)
    valid: list[tuple[int, float]] = []
    for point in points:
        if str(point.get("status", "ok")) != "ok":
            continue
        try:
            k = int(point["k"])
            half_width = float(point["ci95_half_width"])
        except (KeyError, TypeError, ValueError):
            continue
        if k > 0 and math.isfinite(half_width) and half_width > 0.0:
            valid.append((k, half_width))

    for k, half_width in sorted(valid):
        if half_width <= target:
            return {
                "status": "observed",
                "target_ci95_half_width": target,
                "achieved_observed": True,
                "observed_k": k,
                "estimated_k": k,
                "method": "observed_prefix",
                "basis_ci95_half_width": half_width,
            }

    fit = fit_ci_halfwidth_decay(points) if decay_fit is None else decay_fit
    if fit.get("status") != "ok":
        return {
            "status": "unavailable",
            "target_ci95_half_width": target,
            "achieved_observed": False,
            "observed_k": None,
            "estimated_k": None,
            "method": "unavailable",
            "basis_ci95_half_width": math.nan,
            "reason": fit.get("status", "fit_unavailable"),
        }

    slope = float(fit["slope"])
    intercept = float(fit["intercept"])
    if slope >= 0.0 or not math.isfinite(slope) or not math.isfinite(intercept):
        return {
            "status": "unavailable",
            "target_ci95_half_width": target,
            "achieved_observed": False,
            "observed_k": None,
            "estimated_k": None,
            "method": "unavailable",
            "basis_ci95_half_width": math.nan,
            "reason": "non_decaying_fit",
        }

    estimated = math.exp((math.log(target) - intercept) / slope)
    return {
        "status": "extrapolated",
        "target_ci95_half_width": target,
        "achieved_observed": False,
        "observed_k": None,
        "estimated_k": int(math.ceil(estimated)),
        "method": "log_log_ci_halfwidth_decay",
        "basis_ci95_half_width": valid[-1][1] if valid else math.nan,
    }


def fit_linear_slope(
    points: Iterable[dict[str, float | int]],
    x_key: str,
    y_key: str,
) -> dict[str, Any]:
    usable: list[tuple[float, float]] = []
    for point in points:
        try:
            x = float(point[x_key])
            y = float(point[y_key])
        except (KeyError, TypeError, ValueError):
            return {
                "status": "non_finite_or_missing_value",
                "n": len(usable),
                "slope": math.nan,
                "intercept": math.nan,
                "slope_standard_error": math.nan,
                "slope_ci95_low": math.nan,
                "slope_ci95_high": math.nan,
            }
        if not math.isfinite(x) or not math.isfinite(y):
            return {
                "status": "non_finite_or_missing_value",
                "n": len(usable),
                "slope": math.nan,
                "intercept": math.nan,
                "slope_standard_error": math.nan,
                "slope_ci95_low": math.nan,
                "slope_ci95_high": math.nan,
            }
        usable.append((x, y))

    n = len(usable)
    if n < 3:
        return {
            "status": "insufficient_points",
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
    if sxx <= 0.0 or not math.isfinite(sxx):
        return {
            "status": "constant_x",
            "n": n,
            "slope": math.nan,
            "intercept": math.nan,
            "slope_standard_error": math.nan,
            "slope_ci95_low": math.nan,
            "slope_ci95_high": math.nan,
        }

    slope = sum((x - x_mean) * (y - y_mean) for x, y in usable) / sxx
    intercept = y_mean - slope * x_mean
    residual_sse = sum((y - (intercept + slope * x)) ** 2 for x, y in usable)
    df = n - 2
    residual_var = residual_sse / df if df > 0 else 0.0
    slope_se = math.sqrt(residual_var / sxx)
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


def first_ci_overlap_saturation(
    points: Iterable[dict[str, float | int]],
    x_key: str,
    mean_key: str,
    ci_low_key: str,
    ci_high_key: str,
) -> dict[str, Any]:
    rows: list[dict[str, float]] = []
    for point in points:
        try:
            row = {
                x_key: float(point[x_key]),
                mean_key: float(point[mean_key]),
                ci_low_key: float(point[ci_low_key]),
                ci_high_key: float(point[ci_high_key]),
            }
        except (KeyError, TypeError, ValueError):
            return {
                "status": "non_finite_or_missing_value",
                "saturated": False,
                "saturation_x": math.nan,
                "saturation_index": None,
                "overlapping_pair": None,
                "post_saturation_fit": fit_linear_slope([], x_key, mean_key),
            }
        if not all(math.isfinite(value) for value in row.values()):
            return {
                "status": "non_finite_or_missing_value",
                "saturated": False,
                "saturation_x": math.nan,
                "saturation_index": None,
                "overlapping_pair": None,
                "post_saturation_fit": fit_linear_slope([], x_key, mean_key),
            }
        if row[ci_low_key] > row[ci_high_key]:
            return {
                "status": "invalid_ci_interval",
                "saturated": False,
                "saturation_x": math.nan,
                "saturation_index": None,
                "overlapping_pair": None,
                "post_saturation_fit": fit_linear_slope([], x_key, mean_key),
            }
        rows.append(row)

    if len(rows) < 2:
        return {
            "status": "insufficient_points",
            "saturated": False,
            "saturation_x": math.nan,
            "saturation_index": None,
            "overlapping_pair": None,
            "post_saturation_fit": fit_linear_slope([], x_key, mean_key),
        }

    for left_index, (left, right) in enumerate(zip(rows, rows[1:])):
        overlap_low = max(left[ci_low_key], right[ci_low_key])
        overlap_high = min(left[ci_high_key], right[ci_high_key])
        if overlap_low <= overlap_high:
            saturation_index = left_index + 1
            return {
                "status": "ok",
                "saturated": True,
                "saturation_x": float(right[x_key]),
                "saturation_index": saturation_index,
                "overlapping_pair": {
                    "left_index": left_index,
                    "right_index": saturation_index,
                    "left_x": float(left[x_key]),
                    "right_x": float(right[x_key]),
                    "left_ci_low": float(left[ci_low_key]),
                    "left_ci_high": float(left[ci_high_key]),
                    "right_ci_low": float(right[ci_low_key]),
                    "right_ci_high": float(right[ci_high_key]),
                    "overlap_low": float(overlap_low),
                    "overlap_high": float(overlap_high),
                },
                "post_saturation_fit": fit_linear_slope(rows[saturation_index:], x_key, mean_key),
            }

    return {
        "status": "no_adjacent_ci_overlap",
        "saturated": False,
        "saturation_x": math.nan,
        "saturation_index": None,
        "overlapping_pair": None,
        "post_saturation_fit": fit_linear_slope([], x_key, mean_key),
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
