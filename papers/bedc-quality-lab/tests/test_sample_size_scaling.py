import json
import math

import pytest

from scripts import run_sample_size_scaling as scaling


def record(sample_count, seed, value, *, proxy=None, quality_q=None):
    metrics = {name: 1.0 for name in scaling.METRIC_NAMES}
    metrics["linear_identifiability_r2"] = value
    metrics["approx_identifiability_proxy"] = value if proxy is None else proxy
    metrics["quality_q"] = value if quality_q is None else quality_q
    return {
        "sample_count": sample_count,
        "seed_index": seed,
        "seed": 1000 + seed,
        "rho": scaling.RHO,
        "run_id": f"fixture-{sample_count}-{seed}",
        "classifier_name": "fixture-classifier",
        "classifier_training": "fixture-training",
        "metrics": metrics,
        "envelope": {"run_id": f"fixture-{sample_count}-{seed}"},
    }


def records_from_offsets(offsets_by_sample_count):
    rows = []
    for sample_count, offsets in offsets_by_sample_count.items():
        for index, offset in enumerate(offsets):
            rows.append(record(sample_count, index, 0.9 + offset))
    return rows


def test_child_seed_is_deterministic_streamed_and_32_bit():
    first = [scaling._child_seed(445021, index) for index in range(8)]
    second = [scaling._child_seed(445021, index) for index in range(8)]
    alternate = [scaling._child_seed(445022, index) for index in range(8)]

    assert first == second
    assert first != alternate
    assert len(set(first)) == len(first)
    assert all(0 <= seed <= 0xFFFFFFFF for seed in first + alternate)
    assert scaling._child_seed(2**63 - 1, 99) <= 0xFFFFFFFF


def test_aggregate_passes_monotonic_scaling_on_synthetic_records(monkeypatch):
    monkeypatch.setattr(scaling, "SAMPLE_COUNTS", (100, 200, 400, 800, 1600))
    rows = records_from_offsets(
        {
            100: [-0.20, 0.00, 0.20],
            200: [-0.141421356, 0.00, 0.141421356],
            400: [-0.10, 0.00, 0.10],
            800: [-0.070710678, 0.00, 0.070710678],
            1600: [-0.05, 0.00, 0.05],
        }
    )

    aggregate = scaling._aggregate(rows)
    variance = aggregate["variance_scaling"]

    assert aggregate["sample_counts"]["100"]["metrics"]["linear_identifiability_r2"]["n"] == 3
    assert aggregate["sample_counts"]["100"]["metrics"]["linear_identifiability_r2"]["mean"] == pytest.approx(0.9)
    assert variance["monotonic_nonincreasing"]
    assert variance["slope_in_acceptance_interval"]
    assert variance["prediction_pass"]
    assert variance["log_log_fit"]["slope"] == pytest.approx(-0.5, abs=0.02)


def test_aggregate_fails_closed_when_std_does_not_shrink(monkeypatch):
    monkeypatch.setattr(scaling, "SAMPLE_COUNTS", (100, 200, 400, 800, 1600))
    rows = records_from_offsets(
        {
            100: [-0.05, 0.00, 0.05],
            200: [-0.06, 0.00, 0.06],
            400: [-0.07, 0.00, 0.07],
            800: [-0.08, 0.00, 0.08],
            1600: [-0.09, 0.00, 0.09],
        }
    )

    variance = scaling._aggregate(rows)["variance_scaling"]

    assert not variance["monotonic_nonincreasing"]
    assert not variance["slope_in_acceptance_interval"]
    assert variance["prediction_pass"] is False


def test_fit_log_log_slope_reports_ci():
    points = [
        {"sample_count": 100, "std": 0.2},
        {"sample_count": 200, "std": 0.141421356},
        {"sample_count": 400, "std": 0.1},
        {"sample_count": 800, "std": 0.070710678},
        {"sample_count": 1600, "std": 0.05},
    ]

    fit = scaling._fit_log_log_slope(points)

    assert fit["status"] == "ok"
    assert fit["n"] == 5
    assert fit["slope"] == pytest.approx(-0.5, abs=0.001)
    assert fit["slope_ci95_low"] <= fit["slope"] <= fit["slope_ci95_high"]


def test_render_report_contains_required_sections(monkeypatch):
    monkeypatch.setattr(scaling, "SAMPLE_COUNTS", (100, 200, 400, 800, 1600))
    rows = records_from_offsets(
        {
            100: [-0.20, 0.00, 0.20],
            200: [-0.141421356, 0.00, 0.141421356],
            400: [-0.10, 0.00, 0.10],
            800: [-0.070710678, 0.00, 0.070710678],
            1600: [-0.05, 0.00, 0.05],
        }
    )
    payload = scaling._payload(rows)

    report = scaling._render_report(payload)

    assert "# Sample-Size Scaling Experiment" in report
    assert "## Metric Error Bars" in report
    assert "## Variance Scaling Conclusion" in report
    assert "## Applicability Boundary" in report
    assert "## Source Artifacts" in report
    assert "| 100 | `linear_identifiability_r2` | 0.900000" in report
    assert "Prediction result: `pass`" in report


def test_main_writes_payload_shape(monkeypatch, tmp_path):
    monkeypatch.setattr(scaling, "ROOT", tmp_path)
    monkeypatch.setattr(scaling, "SAMPLE_COUNTS", (100, 200, 400, 800, 1600))
    monkeypatch.setattr(
        scaling,
        "_records",
        lambda: records_from_offsets(
            {
                100: [-0.20, 0.00, 0.20],
                200: [-0.141421356, 0.00, 0.141421356],
                400: [-0.10, 0.00, 0.10],
                800: [-0.070710678, 0.00, 0.070710678],
                1600: [-0.05, 0.00, 0.05],
            }
        ),
    )

    scaling.main()

    payload = json.loads((tmp_path / scaling.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / scaling.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == scaling.JSON_ARTIFACT
    assert payload["report"] == scaling.REPORT_ARTIFACT
    assert payload["source_artifacts"]["generation_script"] == "scripts/run_sample_size_scaling.py"
    assert payload["source_artifacts"]["canonical_runner"].endswith("run_experiment")
    assert len(payload["records"]) == 15
    assert payload["aggregate"]["variance_scaling"]["prediction_pass"]
    assert "Sample count range: `100` to `1600`." in report

