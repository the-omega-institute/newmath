import json
from types import SimpleNamespace

import pytest

from scripts import run_rho_identifiability_dose_response as rho_runner


def envelope_for(kwargs, metrics):
    return SimpleNamespace(
        classifier_spec={"name": "fixture-classifier", "training": "fixture-training"},
        metrics=metrics,
        to_dict=lambda: {
            "run_id": kwargs["run_id"],
            "source_spec": {
                "sample_count": kwargs["sample_count"],
                "rho": kwargs["rho"],
            },
            "classifier_spec": {
                "name": "fixture-classifier",
                "training": "fixture-training",
            },
            "metrics": dict(metrics),
            "artifacts": {
                "envelope": kwargs["envelope_artifact"],
                "report": kwargs["report_artifact"],
            },
        },
    )


def metric_row(rho, seed_index, value):
    metrics = {name: 1.0 for name in rho_runner.METRIC_NAMES}
    metrics[rho_runner.TARGET_METRIC] = value
    seed = 1000 + seed_index
    return {
        "sample_count": rho_runner.SAMPLE_COUNT,
        "rho": rho,
        "seed_index": seed_index,
        "seed": seed,
        "run_id": f"fixture-rho-{rho}-seed-{seed}",
        "classifier_name": "fixture-classifier",
        "classifier_training": "fixture-training",
        "metrics": metrics,
        "envelope": {"run_id": f"fixture-rho-{rho}-seed-{seed}"},
    }


def synthetic_records(*, means=None, offsets=None):
    means = means or {
        0.0: 0.20,
        0.25: 0.45,
        0.5: 0.55,
        0.75: 0.56,
        0.9: 0.57,
    }
    offsets = offsets or [-0.01, 0.0, 0.01]
    rows = []
    for rho in rho_runner.RHO_VALUES:
        for seed_index, offset in enumerate(offsets):
            rows.append(metric_row(rho, seed_index, means[rho] + offset))
    return rows


def test_default_grid_has_expected_record_floor():
    assert rho_runner.SAMPLE_COUNT == 384
    assert rho_runner.RHO_VALUES == (0.0, 0.25, 0.5, 0.75, 0.9)
    assert rho_runner.SEED_COUNT >= 15
    assert rho_runner.TARGET_METRIC == "linear_identifiability_r2"
    assert len(rho_runner.RHO_VALUES) * rho_runner.SEED_COUNT >= 75


def test_records_enumerates_grid_and_passes_runner_arguments(monkeypatch):
    calls = []
    monkeypatch.setattr(rho_runner, "RHO_VALUES", (0.0, 0.5))
    monkeypatch.setattr(rho_runner, "SEED_COUNT", 2)

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        metrics = {name: 10.0 for name in rho_runner.METRIC_NAMES}
        metrics[rho_runner.TARGET_METRIC] = kwargs["rho"] + 0.1
        return envelope_for(kwargs, metrics)

    monkeypatch.setattr(rho_runner, "run_experiment", fake_run_experiment)

    rows = rho_runner._records()

    assert len(rows) == 4
    assert calls[0] == {
        "use_torch": rho_runner.USE_TORCH,
        "sample_count": rho_runner.SAMPLE_COUNT,
        "seed": rho_runner._seeds(rho_runner.MASTER_SEED, 2)[0],
        "rho": 0.0,
        "run_id": (
            f"rho-identifiability-dose-response-rho-0p0-seed-"
            f"{rho_runner._seeds(rho_runner.MASTER_SEED, 2)[0]}"
        ),
        "envelope_artifact": rho_runner.JSON_ARTIFACT,
        "report_artifact": rho_runner.REPORT_ARTIFACT,
    }
    assert {row["rho"] for row in rows} == {0.0, 0.5}
    assert rows[0]["metrics"][rho_runner.TARGET_METRIC] == pytest.approx(0.1)
    assert rows[0]["envelope"]["artifacts"] == {
        "envelope": rho_runner.JSON_ARTIFACT,
        "report": rho_runner.REPORT_ARTIFACT,
    }


def test_aggregate_reports_per_rho_mean_std_and_ci(monkeypatch):
    monkeypatch.setattr(rho_runner, "RHO_VALUES", (0.0, 0.25, 0.5, 0.75, 0.9))

    aggregate = rho_runner._aggregate(synthetic_records(offsets=[-0.2, 0.0, 0.2]))
    cell = aggregate["by_rho"]["rho_0p0"]
    metric = cell["metrics"][rho_runner.TARGET_METRIC]

    assert cell["record_count"] == 3
    assert metric["n"] == 3
    assert metric["mean"] == pytest.approx(0.2)
    assert metric["std"] == pytest.approx(0.2)
    assert metric["ci95_half_width"] == pytest.approx(1.96 * 0.2 / (3**0.5))
    assert metric["ci95_low"] < metric["mean"] < metric["ci95_high"]


def test_monotonicity_test_passes_and_fails(monkeypatch):
    monkeypatch.setattr(rho_runner, "RHO_VALUES", (0.0, 0.25, 0.5, 0.75, 0.9))
    passing = rho_runner._target_points(rho_runner._aggregate(synthetic_records()))
    failing = rho_runner._target_points(
        rho_runner._aggregate(
            synthetic_records(
                means={0.0: 0.20, 0.25: 0.45, 0.5: 0.44, 0.75: 0.56, 0.9: 0.57}
            )
        )
    )

    pass_test = rho_runner._monotonicity_test(passing)
    fail_test = rho_runner._monotonicity_test(failing)

    assert pass_test["pass"]
    assert pass_test["nondecreasing"]
    assert fail_test["pass"] is False
    assert fail_test["adjacent_deltas"][1] < 0.0


def test_saturation_estimate_detects_adjacent_ci_overlap(monkeypatch):
    monkeypatch.setattr(rho_runner, "RHO_VALUES", (0.0, 0.25, 0.5, 0.75, 0.9))
    points = rho_runner._target_points(rho_runner._aggregate(synthetic_records()))

    estimate = rho_runner._saturation_estimate(points)

    assert estimate["method"] == "adjacent_ci_overlap_first_rho"
    assert estimate["saturated"]
    assert estimate["saturation_x"] == pytest.approx(0.75)
    assert estimate["saturation_index"] == 3
    assert estimate["grid_boundary"] is False
    assert estimate["overlapping_pair"]["left_x"] == pytest.approx(0.5)
    assert estimate["overlapping_pair"]["right_x"] == pytest.approx(0.75)


def test_saturation_estimate_marks_final_rho_overlap_as_grid_boundary(monkeypatch):
    monkeypatch.setattr(rho_runner, "RHO_VALUES", (0.0, 0.25, 0.5, 0.75, 0.9))
    points = rho_runner._target_points(
        rho_runner._aggregate(
            synthetic_records(
                means={0.0: 0.20, 0.25: 0.45, 0.5: 0.70, 0.75: 0.95, 0.9: 0.96}
            )
        )
    )

    estimate = rho_runner._saturation_estimate(points)

    assert estimate["method"] == "adjacent_ci_overlap_first_rho"
    assert estimate["saturated"]
    assert estimate["saturation_x"] == pytest.approx(0.9)
    assert estimate["saturation_index"] == len(points) - 1
    assert estimate["grid_boundary"] is True
    assert estimate["overlapping_pair"]["left_x"] == pytest.approx(0.75)
    assert estimate["overlapping_pair"]["right_x"] == pytest.approx(0.9)


def test_post_saturation_slope_ci_reports_zero_branches():
    contains = {
        "post_saturation_fit": {
            "status": "ok",
            "slope": 0.01,
            "intercept": 0.5,
            "n": 3,
            "slope_standard_error": 0.01,
            "slope_ci95_low": -0.05,
            "slope_ci95_high": 0.07,
        }
    }
    excludes = {
        "post_saturation_fit": {
            "status": "ok",
            "slope": 0.2,
            "intercept": 0.5,
            "n": 3,
            "slope_standard_error": 0.01,
            "slope_ci95_low": 0.10,
            "slope_ci95_high": 0.30,
        }
    }

    assert rho_runner._post_saturation_slope_ci(contains)["contains_zero"]
    assert rho_runner._post_saturation_slope_ci(contains)["criterion_pass"]
    assert rho_runner._post_saturation_slope_ci(excludes)["contains_zero"] is False
    assert rho_runner._post_saturation_slope_ci(excludes)["criterion_pass"] is False


def test_payload_and_markdown_projection_include_required_fields(monkeypatch):
    monkeypatch.setattr(rho_runner, "RHO_VALUES", (0.0, 0.25, 0.5, 0.75, 0.9))

    payload = rho_runner._payload(synthetic_records())
    report = rho_runner._render_report(payload)

    assert payload["artifact"] == rho_runner.JSON_ARTIFACT
    assert payload["report"] == rho_runner.REPORT_ARTIFACT
    assert set(payload) >= {
        "config",
        "records",
        "aggregate",
        "monotonicity_test",
        "dose_response_fit",
        "saturation_estimate",
        "post_saturation_slope_ci",
        "applicability_boundary",
        "source_artifacts",
    }
    assert "by_rho" in payload["aggregate"]
    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_rho_identifiability_dose_response.py"
    )
    assert payload["source_artifacts"]["shared_stats_helper"] == "scripts/experiment_stats.py"
    assert "bedc_quality_lab.metrics.metric_bundle" in payload["source_artifacts"][
        "import_dependency_chain"
    ]
    assert payload["applicability_boundary"]["sample_count"] == rho_runner.SAMPLE_COUNT
    assert payload["monotonicity_test"]["pass"]
    assert payload["saturation_estimate"]["saturated"]

    assert "# Rho Identifiability Dose-Response Experiment" in report
    assert "## Per-Rho Confidence Intervals" in report
    assert "## Monotonicity" in report
    assert "## Saturation Estimate" in report
    assert "## Post-Saturation Slope" in report
    assert "## Applicability Boundary" in report
    assert "## Source Artifacts" in report
    assert "| 0.0 | 0.200000 +/- 0.010000 |" in report
    assert "Result: `pass`" in report


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(rho_runner, "ROOT", tmp_path)
    monkeypatch.setattr(rho_runner, "RHO_VALUES", (0.0, 0.25, 0.5, 0.75, 0.9))
    monkeypatch.setattr(rho_runner, "_records", synthetic_records)

    rho_runner.main()

    payload = json.loads((tmp_path / rho_runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / rho_runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert len(payload["records"]) == 15
    assert payload["monotonicity_test"]["pass"]
    assert payload["saturation_estimate"]["saturated"]
    assert payload["source_artifacts"]["json_artifact"] == rho_runner.JSON_ARTIFACT
    assert "Total records: `15`" in report
    assert "Rho set: `0.0, 0.25, 0.5, 0.75, 0.9`." in report
