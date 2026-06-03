import math

import pytest

from scripts import run_gap_head_threshold_sweep as sweep


def _cell(mean, *, n=4):
    return {
        "mean": float(mean),
        "std": 0.0,
        "n": int(n),
        "ci95_low": float(mean),
        "ci95_high": float(mean),
    }


def _config():
    return sweep.ThresholdSweepConfig(
        sample_count=128,
        seeds=(11, 22, 33, 44),
        rho=0.55,
        use_torch=False,
        thresholds=sweep.THRESHOLDS,
        json_artifact=sweep.JSON_ARTIFACT,
        report_artifact=sweep.REPORT_ARTIFACT,
        run_id_prefix="fixture-threshold-frontier",
    )


def _record(seed, *, positive_thresholds=(), undefined=False):
    metrics = {}
    control = {}
    positives = {round(float(value), 2) for value in positive_thresholds}
    for threshold in sweep.THRESHOLDS:
        auroc = 0.82 if round(float(threshold), 2) in positives else 0.50
        critical_unlogged = 0.20 if threshold <= 0.50 else 0.40
        metrics[f"{threshold:.2f}"] = {
            "AUROC": auroc,
            "UnloggedErrorRate": 0.15 + threshold * 0.02,
            "LoggedFalseAlarmRate": max(0.0, 0.45 - threshold * 0.25),
            "CriticalUnloggedErrorRate": critical_unlogged,
            "QualityQ": 0.25,
            "NetInformation": auroc + (1.0 - critical_unlogged) - 0.10,
        }
        control[f"{threshold:.2f}"] = {
            "AUROC": 0.50,
            "UnloggedErrorRate": 0.20,
            "LoggedFalseAlarmRate": 0.0,
            "CriticalUnloggedErrorRate": 0.30,
            "QualityQ": 0.25,
            "NetInformation": 1.0,
        }
    return {
        "seed": int(seed),
        "threshold_metrics": metrics,
        "control_baseline_threshold_metrics": control,
        "undefined_metric_reasons": (
            [{"metric": "AUROC", "reason": "constant_label", "seed": int(seed)}]
            if undefined
            else []
        ),
    }


def _records(*, positive_thresholds=(), undefined=False):
    return [
        _record(seed, positive_thresholds=positive_thresholds, undefined=undefined)
        for seed in _config().seeds
    ]


def test_threshold_grid_and_metric_cells_are_complete():
    payload = sweep._payload(
        _records(positive_thresholds=(0.20, 0.25, 0.30)),
        _config(),
        generated_at="fixture-time",
    )

    assert [row["threshold"] for row in payload["threshold_curve"]] == list(sweep.THRESHOLDS)
    for row in payload["threshold_curve"]:
        assert set(row["metrics"]) == set(sweep.METRIC_NAMES)
        for cell in row["metrics"].values():
            assert set(cell) == {"mean", "std", "n", "ci95_low", "ci95_high"}
            assert cell["n"] == len(_config().seeds)
            assert math.isfinite(cell["ci95_low"])
            assert math.isfinite(cell["ci95_high"])
    assert "threshold_records" not in payload


def test_pareto_frontier_uses_only_auroc_and_critical_logged_coverage():
    curve = [
        {
            "threshold": 0.10,
            "metrics": {
                "AUROC": _cell(0.70),
                "CriticalUnloggedErrorRate": _cell(0.40),
                "QualityQ": _cell(10.0),
                "NetInformation": _cell(10.0),
            },
        },
        {
            "threshold": 0.20,
            "metrics": {
                "AUROC": _cell(0.80),
                "CriticalUnloggedErrorRate": _cell(0.20),
                "QualityQ": _cell(-10.0),
                "NetInformation": _cell(-10.0),
            },
        },
        {
            "threshold": 0.30,
            "metrics": {
                "AUROC": _cell(0.82),
                "CriticalUnloggedErrorRate": _cell(0.60),
                "QualityQ": _cell(-20.0),
                "NetInformation": _cell(-20.0),
            },
        },
    ]

    frontier = sweep._pareto_frontier(curve)

    assert [row["threshold"] for row in frontier] == [0.20, 0.30]
    assert sweep._dominates(curve[1], curve[0])
    assert not sweep._dominates(curve[0], curve[1])


def test_hardgate_allows_d5_ready_for_adjacent_positive_controlled_run():
    payload = sweep._payload(
        _records(positive_thresholds=(0.20, 0.25, 0.30)),
        _config(),
        generated_at="fixture-time",
    )

    assert payload["hardgate"]["status"] == "pass"
    assert payload["hardgate"]["checks"]["HG-GH-T1"]["status"] == "pass"
    assert payload["hardgate"]["checks"]["HG-GH-T2"]["status"] == "pass"
    assert payload["hardgate"]["checks"]["HG-GH-T3"]["status"] == "pass"
    assert payload["hardgate"]["checks"]["HG-GH-T4"]["status"] == "pass"
    assert payload["readiness"]["status"] == "D5-ready"


def test_single_positive_threshold_is_only_d4_at_threshold():
    payload = sweep._payload(
        _records(positive_thresholds=(0.25,)),
        _config(),
        generated_at="fixture-time",
    )

    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["checks"]["HG-GH-T3"]["status"] == "pass"
    assert payload["hardgate"]["checks"]["HG-GH-T4"]["status"] == "fail"
    assert payload["readiness"]["status"] == "D4-at-threshold"
    assert payload["readiness"]["positive_thresholds"] == [0.25]


def test_degenerate_metric_keeps_cells_and_invalidates_hardgate():
    payload = sweep._payload(
        _records(positive_thresholds=(0.20, 0.25, 0.30), undefined=True),
        _config(),
        generated_at="fixture-time",
    )

    assert payload["hardgate"]["status"] == "invalid"
    assert payload["hardgate"]["undefined_metric_reasons"]
    for row in payload["threshold_curve"]:
        assert set(row["metrics"]["AUROC"]) == {"mean", "std", "n", "ci95_low", "ci95_high"}


def test_threshold_metrics_for_seed_uses_threshold_projection():
    probabilities = pytest.importorskip("numpy").array(
        [
            [0.90, 0.10, 0.20, 0.30],
            [0.30, 0.10, 0.20, 0.30],
            [0.80, 0.10, 0.20, 0.30],
            [0.20, 0.10, 0.20, 0.30],
        ],
        dtype=float,
    )
    errors = pytest.importorskip("numpy").array([1.0, 1.0, 0.0, 0.0], dtype=float)

    row = sweep._threshold_metrics_for_seed(
        threshold=0.50,
        probabilities=probabilities,
        eval_error=errors,
        quality_q=0.4,
    )

    assert row["UnloggedErrorRate"] == pytest.approx(0.25)
    assert row["LoggedFalseAlarmRate"] == pytest.approx(0.25)
    assert row["CriticalUnloggedErrorRate"] == pytest.approx(0.25)
    assert row["QualityQ"] == pytest.approx(0.4)
