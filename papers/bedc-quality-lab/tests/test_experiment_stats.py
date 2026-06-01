import math

import pytest

from scripts import experiment_stats as stats


def test_sample_std_reports_sample_standard_deviation():
    assert stats.sample_std([]) == 0.0
    assert stats.sample_std([0.73]) == 0.0
    assert stats.sample_std([1.0, 3.0]) == pytest.approx(math.sqrt(2.0))


def test_metric_stats_reports_mean_std_and_ci():
    summary = stats.metric_stats([1.0, 2.0, 3.0])

    assert summary["n"] == 3
    assert summary["mean"] == pytest.approx(2.0)
    assert summary["std"] == pytest.approx(1.0)
    assert summary["ci95_half_width"] == pytest.approx(1.96 / math.sqrt(3.0))
    assert summary["ci95_low"] == pytest.approx(2.0 - 1.96 / math.sqrt(3.0))
    assert summary["ci95_high"] == pytest.approx(2.0 + 1.96 / math.sqrt(3.0))


def test_metric_stats_reports_empty_metric_list_as_closed_nan_payload():
    summary = stats.metric_stats([])

    assert summary["n"] == 0
    assert math.isnan(summary["mean"])
    assert math.isnan(summary["std"])
    assert math.isnan(summary["ci95_half_width"])
    assert math.isnan(summary["ci95_low"])
    assert math.isnan(summary["ci95_high"])


def test_metric_stats_reports_single_record_zero_std_and_ci():
    summary = stats.metric_stats([0.73])

    assert summary == {
        "n": 1,
        "mean": pytest.approx(0.73),
        "std": 0.0,
        "ci95_half_width": 0.0,
        "ci95_low": pytest.approx(0.73),
        "ci95_high": pytest.approx(0.73),
    }


def test_fit_log_log_slope_reports_ci():
    points = [
        {"sample_count": 100, "std": 0.2},
        {"sample_count": 200, "std": 0.141421356},
        {"sample_count": 400, "std": 0.1},
        {"sample_count": 800, "std": 0.070710678},
        {"sample_count": 1600, "std": 0.05},
    ]

    fit = stats.fit_log_log_slope(points)

    assert fit["status"] == "ok"
    assert fit["n"] == 5
    assert fit["slope"] == pytest.approx(-0.5, abs=0.001)
    assert fit["slope_ci95_low"] <= fit["slope"] <= fit["slope_ci95_high"]


def test_fit_log_log_slope_fails_closed_for_insufficient_positive_std_points():
    fit = stats.fit_log_log_slope(
        [
            {"sample_count": 100, "std": 0.0},
            {"sample_count": 200, "std": 0.1},
            {"sample_count": 400, "std": 0.0},
            {"sample_count": 800, "std": 0.2},
        ]
    )

    assert fit["status"] == "insufficient_positive_std"
    assert fit["n"] == 2
    assert math.isnan(fit["slope"])
    assert math.isnan(fit["intercept"])
    assert math.isnan(fit["slope_standard_error"])
    assert math.isnan(fit["slope_ci95_low"])
    assert math.isnan(fit["slope_ci95_high"])


def test_fit_linear_slope_reports_slope_and_ci():
    points = [
        {"debt_level": 0.0, "quality_q": 0.95},
        {"debt_level": 0.1, "quality_q": 0.85},
        {"debt_level": 0.2, "quality_q": 0.75},
        {"debt_level": 0.3, "quality_q": 0.65},
        {"debt_level": 0.4, "quality_q": 0.55},
    ]

    fit = stats.fit_linear_slope(points, "debt_level", "quality_q")

    assert fit["status"] == "ok"
    assert fit["n"] == 5
    assert fit["slope"] == pytest.approx(-1.0)
    assert fit["intercept"] == pytest.approx(0.95)
    assert fit["slope_standard_error"] == pytest.approx(0.0)
    assert fit["slope_ci95_low"] <= fit["slope"] <= fit["slope_ci95_high"]


def test_fit_linear_slope_fails_closed_for_non_finite_and_insufficient_points():
    non_finite = stats.fit_linear_slope(
        [
            {"debt_level": 0.0, "quality_q": 0.95},
            {"debt_level": 0.1, "quality_q": math.inf},
            {"debt_level": 0.2, "quality_q": 0.75},
        ],
        "debt_level",
        "quality_q",
    )
    insufficient = stats.fit_linear_slope(
        [
            {"debt_level": 0.0, "quality_q": 0.95},
            {"debt_level": 0.1, "quality_q": 0.85},
        ],
        "debt_level",
        "quality_q",
    )

    assert non_finite["status"] == "non_finite_or_missing_value"
    assert math.isnan(non_finite["slope"])
    assert math.isnan(non_finite["slope_ci95_low"])
    assert insufficient["status"] == "insufficient_points"
    assert insufficient["n"] == 2
    assert math.isnan(insufficient["slope"])


def test_fit_linear_slope_fails_closed_for_constant_x():
    fit = stats.fit_linear_slope(
        [
            {"debt_level": 1.0, "quality_q": 0.95},
            {"debt_level": 1.0, "quality_q": 0.85},
            {"debt_level": 1.0, "quality_q": 0.75},
        ],
        "debt_level",
        "quality_q",
    )

    assert fit["status"] == "constant_x"
    assert fit["n"] == 3
    assert math.isnan(fit["slope"])
    assert math.isnan(fit["intercept"])
    assert math.isnan(fit["slope_standard_error"])
    assert math.isnan(fit["slope_ci95_low"])
    assert math.isnan(fit["slope_ci95_high"])


def test_slope_ci_overlap_true_and_false():
    left = {"status": "ok", "slope_ci95_low": -0.7, "slope_ci95_high": -0.3}
    overlapping = {"status": "ok", "slope_ci95_low": -0.5, "slope_ci95_high": -0.1}
    separated = {"status": "ok", "slope_ci95_low": 0.1, "slope_ci95_high": 0.2}

    assert stats.slope_ci_overlap(left, overlapping)
    assert not stats.slope_ci_overlap(left, separated)


def test_all_slope_ci_overlap_requires_common_intersection():
    fits = [
        {"status": "ok", "slope_ci95_low": -0.7, "slope_ci95_high": -0.2},
        {"status": "ok", "slope_ci95_low": -0.5, "slope_ci95_high": -0.1},
        {"status": "ok", "slope_ci95_low": -0.45, "slope_ci95_high": 0.0},
    ]
    separated = [
        {"status": "ok", "slope_ci95_low": -0.7, "slope_ci95_high": -0.5},
        {"status": "ok", "slope_ci95_low": -0.4, "slope_ci95_high": -0.1},
    ]

    common = stats.slope_ci_common_overlap(fits)

    assert stats.all_slope_ci_overlap(fits)
    assert common["status"] == "ok"
    assert common["overlap_low"] == pytest.approx(-0.45)
    assert common["overlap_high"] == pytest.approx(-0.2)
    assert not stats.all_slope_ci_overlap(separated)


def test_prefix_metric_stats_uses_only_first_k_values():
    rows = stats.prefix_metric_stats([1.0, 3.0, 100.0, 1000.0], [2])

    assert rows[0]["status"] == "ok"
    assert rows[0]["k"] == 2
    assert rows[0]["mean"] == pytest.approx(2.0)
    assert rows[0]["std"] == pytest.approx(math.sqrt(2.0))


def test_prefix_metric_stats_fails_closed_for_empty_and_insufficient_points():
    empty = stats.prefix_metric_stats([], [2])[0]
    single = stats.prefix_metric_stats([0.7], [1, 2])

    assert empty["status"] == "insufficient_points"
    assert empty["n"] == 0
    assert math.isnan(empty["mean"])
    assert single[0]["status"] == "insufficient_points"
    assert single[1]["status"] == "insufficient_points"
    assert math.isnan(single[0]["ci95_half_width"])


def test_prefix_metric_stats_fails_closed_for_non_finite_prefix_values():
    rows = stats.prefix_metric_stats([1.0, math.nan, 3.0], [2, 3])

    assert rows[0]["status"] == "non_finite_value"
    assert rows[0]["n"] == 2
    assert rows[1]["status"] == "non_finite_value"
    assert rows[1]["n"] == 3
    assert math.isnan(rows[0]["mean"])
    assert math.isnan(rows[1]["ci95_half_width"])


def test_prefix_metric_stats_half_width_is_nonincreasing_for_synthetic_shrinkage():
    values = [1.0, 1.1, 0.95, 1.04, 1.02, 1.01, 0.99, 1.0]
    rows = stats.prefix_metric_stats(values, [2, 4, 8])
    half_widths = [float(row["ci95_half_width"]) for row in rows]

    assert all(row["status"] == "ok" for row in rows)
    assert half_widths[1] <= half_widths[0]
    assert half_widths[2] <= half_widths[1]


def test_fit_ci_halfwidth_decay_reports_root_k_slope():
    rows = [
        {"k": 5, "status": "ok", "ci95_half_width": 0.2},
        {"k": 10, "status": "ok", "ci95_half_width": 0.2 / math.sqrt(2.0)},
        {"k": 20, "status": "ok", "ci95_half_width": 0.1},
        {"k": 40, "status": "ok", "ci95_half_width": 0.1 / math.sqrt(2.0)},
    ]

    fit = stats.fit_ci_halfwidth_decay(rows)

    assert fit["status"] == "ok"
    assert fit["slope"] == pytest.approx(-0.5, abs=0.001)
    assert fit["slope_in_expected_interval"]
    assert fit["usable_points"] == [
        {"k": 5, "ci95_half_width": pytest.approx(0.2)},
        {"k": 10, "ci95_half_width": pytest.approx(0.2 / math.sqrt(2.0))},
        {"k": 20, "ci95_half_width": pytest.approx(0.1)},
        {"k": 40, "ci95_half_width": pytest.approx(0.1 / math.sqrt(2.0))},
    ]


def test_fit_ci_halfwidth_decay_ignores_nonpositive_nonfinite_and_closed_rows():
    fit = stats.fit_ci_halfwidth_decay(
        [
            {"k": 2, "status": "ok", "ci95_half_width": 0.4},
            {"k": 4, "status": "ok", "ci95_half_width": 0.2},
            {"k": 8, "status": "ok", "ci95_half_width": 0.0},
            {"k": 16, "status": "ok", "ci95_half_width": math.inf},
            {"k": 32, "status": "insufficient_points", "ci95_half_width": math.nan},
            {"k": 64, "status": "ok", "ci95_half_width": 0.1},
        ]
    )

    assert fit["status"] == "ok"
    assert [point["k"] for point in fit["usable_points"]] == [2, 4, 64]
    assert [point["status"] for point in fit["ignored_points"]] == [
        "non_positive_or_non_finite_half_width",
        "non_positive_or_non_finite_half_width",
        "insufficient_points",
    ]


def test_fit_ci_halfwidth_decay_ignores_missing_invalid_half_width_and_invalid_k():
    fit = stats.fit_ci_halfwidth_decay(
        [
            {"k": 2, "status": "ok", "ci95_half_width": 0.4},
            {"k": 4, "status": "ok", "ci95_half_width": 0.2},
            {"k": 8, "status": "ok"},
            {"k": 16, "status": "ok", "ci95_half_width": "not-a-number"},
            {"k": 0, "status": "ok", "ci95_half_width": 0.1},
            {"k": -1, "status": "ok", "ci95_half_width": 0.1},
            {"k": math.inf, "status": "ok", "ci95_half_width": 0.1},
            {"k": 64, "status": "ok", "ci95_half_width": 0.1},
        ]
    )

    assert fit["status"] == "ok"
    assert [point["k"] for point in fit["usable_points"]] == [2, 4, 64]
    assert [point["status"] for point in fit["ignored_points"]] == [
        "missing_or_invalid_half_width",
        "missing_or_invalid_half_width",
        "non_positive_or_non_finite_k",
        "non_positive_or_non_finite_k",
        "non_positive_or_non_finite_k",
    ]


def test_estimate_min_k_for_ci_returns_observed_or_extrapolated_k():
    observed_rows = [
        {"k": 5, "status": "ok", "ci95_half_width": 0.04},
        {"k": 10, "status": "ok", "ci95_half_width": 0.015},
    ]
    extrapolated_rows = [
        {"k": 5, "status": "ok", "ci95_half_width": 0.08},
        {"k": 10, "status": "ok", "ci95_half_width": 0.04},
        {"k": 20, "status": "ok", "ci95_half_width": 0.02},
        {"k": 40, "status": "ok", "ci95_half_width": 0.01},
    ]

    observed = stats.estimate_min_k_for_ci(observed_rows, target_ci95_half_width=0.02)
    extrapolated = stats.estimate_min_k_for_ci(
        extrapolated_rows,
        target_ci95_half_width=0.005,
    )

    assert observed["status"] == "observed"
    assert observed["estimated_k"] == 10
    assert observed["achieved_observed"]
    assert extrapolated["status"] == "extrapolated"
    assert extrapolated["estimated_k"] > 40
    assert not extrapolated["achieved_observed"]


def test_estimate_min_k_for_ci_reports_unavailable_for_unusable_fit_data():
    rows = [
        {"k": 5, "status": "ok", "ci95_half_width": 0.05},
        {"k": 10, "status": "insufficient_points", "ci95_half_width": math.nan},
    ]

    estimate = stats.estimate_min_k_for_ci(rows, target_ci95_half_width=0.01)

    assert estimate["status"] == "unavailable"
    assert estimate["estimated_k"] is None
    assert not estimate["achieved_observed"]
    assert estimate["reason"] == "insufficient_positive_std"


def test_estimate_min_k_for_ci_reports_unavailable_for_non_decaying_fit():
    rows = [
        {"k": 5, "status": "ok", "ci95_half_width": 0.08},
        {"k": 10, "status": "ok", "ci95_half_width": 0.07},
        {"k": 20, "status": "ok", "ci95_half_width": 0.06},
    ]
    fit = {"status": "ok", "slope": 0.0, "intercept": -2.0}

    estimate = stats.estimate_min_k_for_ci(
        rows,
        target_ci95_half_width=0.01,
        decay_fit=fit,
    )

    assert estimate["status"] == "unavailable"
    assert estimate["estimated_k"] is None
    assert not estimate["achieved_observed"]
    assert estimate["reason"] == "non_decaying_fit"
