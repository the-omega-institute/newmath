import hashlib
import json
import math
from types import SimpleNamespace

import numpy as np
import pytest

from bedc_quality_lab import schema
from scripts import run_gaussian_ou_gap_ledger_head as gap_runner
from scripts import run_gaussian_ou_gap_ledger_shift_robustness as runner


def _sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _fixture_arrays():
    z = np.array(
        [
            [2.0, 1.0],
            [-2.0, 1.0],
            [2.0, -1.0],
            [-2.0, -1.0],
            [0.25, 0.25],
            [-0.25, -0.25],
        ],
        dtype=np.float64,
    )
    z_pair = np.array(
        [
            [-2.0, 1.0],
            [-2.0, 1.0],
            [2.0, -1.0],
            [2.0, -1.0],
            [2.0, 2.0],
            [-0.25, 0.25],
        ],
        dtype=np.float64,
    )
    return z, z_pair


def _install_small_fixture(monkeypatch):
    calls = {"rho": [], "fit_gap": 0, "predict_gap": 0, "high_threshold": 0}
    z, z_pair = _fixture_arrays()
    train_idx = np.array([1, 2, 3, 4], dtype=np.int64)
    eval_idx = np.array([0, 5], dtype=np.int64)

    def fake_make_toy_batch(sample_count, *, rho, seed):
        calls["rho"].append(float(rho))
        assert sample_count == 6
        assert seed == 4242
        return SimpleNamespace(z=z, z_pair=z_pair)

    def fake_split(n, *, seed):
        assert n == 6
        assert seed == 4242
        return train_idx, eval_idx

    def fake_high_threshold(batch_z, batch_train_idx):
        calls["high_threshold"] += 1
        np.testing.assert_array_equal(batch_train_idx, train_idx)
        return 1.0

    def fake_fit_probe(batch_z, labels):
        return {"name": runner.DISTINCTIONS[calls.setdefault("probe", 0)]}

    def fake_predict_probe(probe, batch_z):
        name = probe["name"]
        value = np.asarray(batch_z, dtype=np.float64)
        labels = gap_runner.distinction._label_truth(name, value, high_energy_threshold=1.0)
        predictions = np.array(labels, copy=True)
        if name == "latent_x_positive":
            predictions[(value[:, 0] > 1.5) & (value[:, 1] > 0.5)] = 0.0
        magnitude = np.where(np.max(np.abs(value), axis=1) < 0.5, 0.05, 2.0)
        logits = np.where(predictions > 0.5, magnitude, -magnitude).astype(np.float64)
        return {
            "probabilities": gap_runner._sigmoid(logits),
            "logits": logits,
            "predictions": predictions.astype(np.float64),
        }

    def fake_fit_probe_ordered(batch_z, labels):
        index = calls.setdefault("fit_probe_count", 0)
        calls["fit_probe_count"] = index + 1
        return {"name": runner.DISTINCTIONS[index % len(runner.DISTINCTIONS)]}

    def fake_run_experiment(**kwargs):
        return SimpleNamespace(
            run_id=kwargs["run_id"],
            source_spec={"sample_count": kwargs["sample_count"], "rho": kwargs["rho"]},
            classifier_spec={"fixture": True},
            metrics={
                "quality_q": 0.25 + float(kwargs["rho"]) * 0.01,
                "quality_margin": 0.75,
                "linear_identifiability_r2": 0.5,
                "approx_identifiability_proxy": 0.125,
            },
            artifacts={
                "envelope": kwargs["envelope_artifact"],
                "report": kwargs["report_artifact"],
            },
        )

    def fake_fit_gap_head(features, labels):
        calls["fit_gap"] += 1
        return {"fixture": "gap-head"}

    def fake_predict_gap_head(heads, features):
        calls["predict_gap"] += 1
        assert heads == {"fixture": "gap-head"}
        return np.array(
            [
                [0.9, 0.2, 0.3, 0.4],
                [0.1, 0.8, 0.2, 0.7],
            ],
            dtype=np.float64,
        )

    monkeypatch.setattr(runner, "SAMPLE_COUNT", 6)
    monkeypatch.setattr(runner, "SEED_COUNT", 1)
    monkeypatch.setattr(runner, "EVAL_RHO_GRID", (0.40, 0.82))
    monkeypatch.setattr(runner, "make_toy_batch", fake_make_toy_batch)
    monkeypatch.setattr(runner, "_split_for_seed", fake_split)
    monkeypatch.setattr(runner.gap_runner.distinction, "_high_energy_threshold", fake_high_threshold)
    monkeypatch.setattr(runner.gap_runner.distinction, "_fit_probe", fake_fit_probe_ordered)
    monkeypatch.setattr(runner.gap_runner.distinction, "_predict_probe", fake_predict_probe)
    monkeypatch.setattr(runner.gap_runner, "run_experiment", fake_run_experiment)
    monkeypatch.setattr(runner.gap_runner, "_fit_gap_head", fake_fit_gap_head)
    monkeypatch.setattr(runner.gap_runner, "_predict_gap_head", fake_predict_gap_head)
    monkeypatch.setattr(runner, "_seeds", lambda: [4242])
    return calls


def test_predeclared_grid_and_seed_floor_include_baseline():
    assert runner.TRAIN_RHO == 0.82
    assert runner.EVAL_RHO_GRID == (0.40, 0.60, 0.82, 0.90, 0.98)
    assert runner.TRAIN_RHO in runner.EVAL_RHO_GRID
    assert runner.SEED_COUNT >= 20
    assert runner.PRIMARY_TAU == gap_runner.PRIMARY_TAU == 0.5
    assert runner.PRIMARY_EPSILON == gap_runner.PRIMARY_EPSILON == 0.0


def test_baseline_gap_head_fit_happens_once_and_is_reused_across_eval_rho(monkeypatch):
    calls = _install_small_fixture(monkeypatch)

    records = runner._records()

    assert calls["fit_gap"] == 1
    assert calls["predict_gap"] == 2
    assert calls["high_threshold"] == 1
    assert calls["fit_probe_count"] == len(runner.DISTINCTIONS)
    assert calls["rho"] == [runner.TRAIN_RHO, 0.40, 0.82]
    assert [record["eval_rho"] for record in records] == [0.40, 0.82]
    assert all(record["config"]["baseline_high_energy_threshold"] == 1.0 for record in records)


def test_each_cell_passes_eval_rho_to_toy_world_and_keeps_shared_error_surface(monkeypatch):
    _install_small_fixture(monkeypatch)

    records = runner._records()

    for record in records:
        assert record["shared_error_surface"]["denominator"] == 2
        vanilla = record["arms"]["vanilla"]
        gap = record["arms"]["gap_head"]
        assert vanilla["prediction_error_rate"] == gap["prediction_error_rate"]
        assert record["comparison"]["unlogged_error_rate_gap_minus_vanilla"] == pytest.approx(
            gap["unlogged_error_rate"] - vanilla["unlogged_error_rate"]
        )
        assert record["split"]["train_indices"] == [1, 2, 3, 4]
        assert record["split"]["eval_indices"] == [0, 5]


def test_cell_metrics_match_imported_gap_runner_helpers():
    labels = np.array(
        [[1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0], [0.0, 0.0, 1.0, 0.0]],
        dtype=np.float64,
    )
    error = np.array([1.0, 0.0, 0.0], dtype=np.float64)
    probabilities = np.array(
        [[0.9, 0.1, 0.1, 0.1], [0.1, 0.9, 0.1, 0.1], [0.1, 0.1, 0.9, 0.1]],
        dtype=np.float64,
    )

    imported = gap_runner._metrics_for_arm(
        arm="gap_head", probabilities=probabilities, labels=labels, prediction_error=error
    )
    projected = runner._metric_projection(imported)

    assert projected["unlogged_error_rate"] == pytest.approx(
        gap_runner._unlogged_error_rate(error, probabilities[:, 0], tau=runner.PRIMARY_TAU)
    )
    assert projected["failure_detection_auroc"] == gap_runner._auroc(error, probabilities[:, 0])
    assert projected["ece"]["value"] == gap_runner._ece(error, probabilities[:, 0])["value"]


def test_aggregate_reports_per_rho_ci_and_delta_of_delta(monkeypatch):
    records = []
    for seed in (1, 2, 3):
        for rho, gap_delta in ((0.40, -0.2), (0.82, -0.4), (0.98, -0.1)):
            records.append(
                {
                    "seed": seed,
                    "eval_rho": rho,
                    "arms": {
                        arm: {
                            "failure_detection_auroc": {"value": 0.5 if arm == "vanilla" else 0.9},
                            "ece": {"value": 0.2},
                            "unlogged_error_rate": 0.4 if arm == "vanilla" else 0.4 + gap_delta,
                            "critical_unlogged_error_rate": 0.4 if arm == "vanilla" else 0.4 + gap_delta,
                            "prediction_error_rate": 0.4,
                            "primary_gap_sound": {
                                "low_gap_implies_error_within_epsilon": 0.6,
                                "error_above_epsilon_implies_gap_at_least_tau": 0.7,
                            },
                        }
                        for arm in ("vanilla", "gap_head")
                    },
                    "comparison": {
                        "unlogged_error_rate_gap_minus_vanilla": gap_delta,
                        "critical_unlogged_error_rate_gap_minus_vanilla": gap_delta,
                        "failure_detection_auroc_gap_minus_vanilla": 0.4,
                        "ece_gap_minus_vanilla": 0.0,
                        "gap_sound_low_gap_implies_error_delta_gap_minus_vanilla": 0.0,
                        "gap_sound_error_above_epsilon_delta_gap_minus_vanilla": 0.0,
                    },
                }
            )
    monkeypatch.setattr(runner, "EVAL_RHO_GRID", (0.40, 0.82, 0.98))

    aggregate = runner._aggregate(records)

    assert aggregate["record_count"] == 9
    assert aggregate["by_eval_rho"][0]["by_arm"]["gap_head"]["unlogged_error_rate"]["n"] == 3
    assert math.isfinite(
        aggregate["by_eval_rho"][0]["by_arm"]["gap_head"]["unlogged_error_rate"][
            "ci95_half_width"
        ]
    )
    assert aggregate["by_eval_rho"][0]["comparison"][
        "unlogged_error_rate_delta_of_delta_relative_to_baseline"
    ]["mean"] == pytest.approx(0.2)
    assert aggregate["advantage_degradation_slope"]["status"] == "ok"


def test_payload_contains_json_source_boundary_negative_result_and_source_artifacts(monkeypatch):
    _install_small_fixture(monkeypatch)
    payload = runner._payload(runner._records())
    report = runner._render_report(payload)

    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_gaussian_ou_gap_ledger_shift_robustness.py"
    )
    assert payload["source_artifacts"]["imported_gap_ledger_head_runner"] == (
        "scripts/run_gaussian_ou_gap_ledger_head.py"
    )
    assert payload["applicability_boundary"]["shift_surface_kind"] == "ou_pair_process"
    assert "observation-noise" in payload["applicability_boundary"]["observation_noise_boundary"]
    assert "negative_result_note" in payload
    assert payload["aggregate"]["expected_record_count"] == 2
    assert "JSON numeric source" in report
    assert "## Applicability Boundary" in report
    assert "## Negative Result Note" in report
    assert "## Source Artifacts" in report


def test_main_writes_json_and_markdown_projection(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(runner, "EVAL_RHO_GRID", (0.82,))
    monkeypatch.setattr(runner, "SEED_COUNT", 1)
    record = {
        "seed": 1,
        "eval_rho": 0.82,
        "arms": {
            arm: {
                "failure_detection_auroc": {"value": 0.75},
                "ece": {"value": 0.2},
                "unlogged_error_rate": 0.1,
                "critical_unlogged_error_rate": 0.1,
                "prediction_error_rate": 0.2,
                "primary_gap_sound": {
                    "low_gap_implies_error_within_epsilon": 0.9,
                    "error_above_epsilon_implies_gap_at_least_tau": 0.8,
                },
            }
            for arm in ("vanilla", "gap_head")
        },
        "comparison": {
            "unlogged_error_rate_gap_minus_vanilla": 0.0,
            "critical_unlogged_error_rate_gap_minus_vanilla": 0.0,
            "failure_detection_auroc_gap_minus_vanilla": 0.0,
            "ece_gap_minus_vanilla": 0.0,
            "gap_sound_low_gap_implies_error_delta_gap_minus_vanilla": 0.0,
            "gap_sound_error_above_epsilon_delta_gap_minus_vanilla": 0.0,
        },
    }
    monkeypatch.setattr(runner, "_records", lambda: [record])

    runner.main()

    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["report"] == runner.REPORT_ARTIFACT
    assert payload["aggregate"]["record_count"] == 1
    assert "# Gaussian-OU Gap-Ledger Shift Robustness" in report
    assert f"JSON numeric source: `{runner.JSON_ARTIFACT}`" in report


def test_schema_package_and_canonical_gap_runner_surfaces_are_not_mutated():
    paths = [
        runner.ROOT / "scripts/run_gaussian_ou_gap_ledger_head.py",
        runner.ROOT / "scripts/run_gaussian_ou_lejepa.py",
        runner.ROOT / "bedc_quality_lab/__init__.py",
    ]
    before = {path: _sha(path) for path in paths}

    assert schema.SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert not hasattr(__import__("bedc_quality_lab"), "ShiftEvaluationCell")

    after = {path: _sha(path) for path in paths}
    assert after == before


def test_non_finite_arrays_fail_closed():
    with pytest.raises(ValueError, match="nonfinite contains non-finite values"):
        runner._require_finite("nonfinite", np.array([1.0, math.nan]), ndim=1)
