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
