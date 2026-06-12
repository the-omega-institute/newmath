import json
from types import SimpleNamespace

import pytest

from scripts import run_seed_count_convergence as convergence


def record(seed_index, seed, value):
    return {
        "seed_index": seed_index,
        "seed_sequence_position": seed_index + 1,
        "seed": seed,
        "sample_count": convergence.SAMPLE_COUNT,
        "rho": convergence.RHO,
        "run_id": f"fixture-seed-{seed}",
        "classifier_name": "fixture-classifier",
        "classifier_training": "fixture-training",
        "source_spec": {"name": "fixture-source"},
        "metrics": {
            convergence.TARGET_METRIC: value,
            "quality_q": value - 1.0,
        },
        "envelope": {
            "run_id": f"fixture-seed-{seed}",
            "source_spec": {"name": "fixture-source"},
            "classifier_spec": {"name": "fixture-classifier", "training": "fixture-training"},
            "metrics": {convergence.TARGET_METRIC: value},
            "artifacts": {
                "envelope": convergence.JSON_ARTIFACT,
                "report": convergence.REPORT_ARTIFACT,
            },
        },
    }


def records_from_values(values):
    return [
        record(index, seed, value)
        for index, (seed, value) in enumerate(zip(convergence._seeds(count=len(values)), values))
    ]


def test_k_max_is_at_least_forty():
    assert convergence.K_MAX >= 40


def test_child_seeds_are_deterministic_stable_unique_and_32_bit():
    first = convergence._seeds(466021, 8)
    second = convergence._seeds(466021, 8)
    alternate = convergence._seeds(466022, 8)

    assert first == second
    assert first != alternate
    assert len(set(first)) == len(first)
    assert all(0 <= seed <= 0xFFFFFFFF for seed in first)


def test_run_record_passes_canonical_runner_arguments_and_copies_fields(monkeypatch):
    calls = []
    metrics = {convergence.TARGET_METRIC: 0.91, "quality_q": -0.2}

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return SimpleNamespace(
            classifier_spec={"name": "fixture-classifier", "training": "fixture-training"},
            source_spec={"name": "fixture-source", "sample_count": kwargs["sample_count"]},
            metrics=metrics,
            to_dict=lambda: {
                "run_id": kwargs["run_id"],
                "source_spec": {"name": "fixture-source"},
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

    monkeypatch.setattr(convergence, "run_experiment", fake_run_experiment)

    row = convergence._run_record(seed=4242, seed_index=3)

    assert calls == [
        {
            "use_torch": convergence.USE_TORCH,
            "sample_count": convergence.SAMPLE_COUNT,
            "rho": convergence.RHO,
            "seed": 4242,
            "run_id": "seed-count-convergence-seed-4242",
            "envelope_artifact": convergence.JSON_ARTIFACT,
            "report_artifact": convergence.REPORT_ARTIFACT,
        }
    ]
    assert row["seed_index"] == 3
    assert row["seed_sequence_position"] == 4
    assert row["classifier_name"] == "fixture-classifier"
    assert row["classifier_training"] == "fixture-training"
    assert row["source_spec"] == {"name": "fixture-source", "sample_count": convergence.SAMPLE_COUNT}
    assert row["metrics"] == metrics
    assert row["envelope"]["artifacts"] == {
        "envelope": convergence.JSON_ARTIFACT,
        "report": convergence.REPORT_ARTIFACT,
    }


def test_k_grid_is_sorted_and_within_k_max():
    grid = convergence._validated_k_grid()

    assert grid == sorted(grid)
    assert len(grid) >= 4
    assert max(grid) <= convergence.K_MAX


def test_running_stats_are_computed_from_prefixes(monkeypatch):
    monkeypatch.setattr(convergence, "K_GRID", (2, 4, 6, 8))
    monkeypatch.setattr(convergence, "K_MAX", 8)
    rows = records_from_values([1.0, 3.0, 100.0, 100.0, 100.0, 100.0, 1000.0, 1000.0])

    running = convergence._running_stats(rows)

    assert running[0]["k"] == 2
    assert running[0]["mean"] == pytest.approx(2.0)
    assert running[1]["mean"] == pytest.approx(51.0)


def test_convergence_conclusion_uses_late_adjacent_mean_delta(monkeypatch):
    monkeypatch.setattr(convergence, "LATE_MEAN_DELTA_THRESHOLD", 0.02)
    running = [
        {"k": 5, "status": "ok", "mean": 0.9},
        {"k": 10, "status": "ok", "mean": 0.92},
        {"k": 20, "status": "ok", "mean": 0.931},
        {"k": 40, "status": "ok", "mean": 0.94},
    ]

    deltas = convergence._convergence_deltas(running)

    assert deltas["deltas"][-1]["from_k"] == 20
    assert deltas["deltas"][-1]["to_k"] == 40
    assert deltas["late_adjacent_mean_delta_within_threshold"]


def test_ci_halfwidth_slope_reports_interval_result(monkeypatch):
    monkeypatch.setattr(convergence, "SLOPE_ACCEPTANCE_INTERVAL", (-0.8, -0.3))
    running = [
        {"k": 5, "status": "ok", "ci95_half_width": 0.2},
        {"k": 10, "status": "ok", "ci95_half_width": 0.2 / 2**0.5},
        {"k": 20, "status": "ok", "ci95_half_width": 0.1},
        {"k": 40, "status": "ok", "ci95_half_width": 0.1 / 2**0.5},
    ]

    fit = convergence._ci_decay_fit(running)

    assert fit["status"] == "ok"
    assert fit["slope"] == pytest.approx(-0.5, abs=0.001)
    assert fit["slope_in_acceptance_interval"]


def test_payload_contains_reports_artifacts_and_boundary(monkeypatch):
    monkeypatch.setattr(convergence, "K_GRID", (5, 10, 20, 40))
    monkeypatch.setattr(convergence, "K_MAX", 40)
    values = [0.9 + ((-1) ** index) * 0.08 / ((index + 1) ** 0.5) for index in range(40)]
    payload = convergence._payload(records_from_values(values))

    assert payload["artifact"] == convergence.JSON_ARTIFACT
    assert payload["report"] == convergence.REPORT_ARTIFACT
    assert payload["source_artifacts"]["generation_script"] == "scripts/run_seed_count_convergence.py"
    assert payload["source_artifacts"]["canonical_runner"].endswith("run_experiment")
    assert payload["applicability_boundary"]["method"] == convergence.METHOD
    assert payload["config"]["method"] == convergence.METHOD
    assert len(payload["records"]) == 40
    assert payload["aggregate"]["record_count"] == 40
    assert len(payload["aggregate"]["running_stats"]) == 4
    assert "minimum_k_estimate" in payload["aggregate"]


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(convergence, "ROOT", tmp_path)
    monkeypatch.setattr(
        convergence,
        "_records",
        lambda: records_from_values(
            [0.9 + ((-1) ** index) * 0.08 / ((index + 1) ** 0.5) for index in range(40)]
        ),
    )

    convergence.main()

    payload = json.loads((tmp_path / convergence.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / convergence.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == convergence.JSON_ARTIFACT
    assert payload["report"] == convergence.REPORT_ARTIFACT
    assert payload["aggregate"]["record_count"] == 40
    assert "## Prefix CI Table" in report
    assert "## Applicability Boundary" in report
    assert "## Source Artifacts" in report
