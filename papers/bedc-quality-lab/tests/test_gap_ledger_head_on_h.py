import json
from types import SimpleNamespace

import numpy as np
import pytest

from scripts import run_gap_ledger_head_on_h as runner


def _record_fixture(monkeypatch):
    sentinel = 987654321.0
    z = np.array(
        [
            [sentinel, -sentinel],
            [-sentinel, sentinel],
            [sentinel, sentinel],
            [-sentinel, -sentinel],
            [sentinel, 0.0],
            [0.0, -sentinel],
        ],
        dtype=np.float64,
    )
    z_pair = -z
    x = np.array(
        [
            [0.0, 0.0],
            [1.0, 0.2],
            [0.2, 1.0],
            [1.0, 1.0],
            [0.4, 0.7],
            [0.8, 0.1],
        ],
        dtype=np.float64,
    )
    x_pair = x + 0.05
    train_idx = np.array([0, 1, 2, 3], dtype=np.int64)
    eval_idx = np.array([4, 5], dtype=np.int64)

    def fake_batch(sample_count, *, rho, seed):
        assert sample_count == 6
        assert rho == runner.RHO
        assert seed == 123
        return SimpleNamespace(z=z, z_pair=z_pair, x=x, x_pair=x_pair)

    def fake_split(n, *, seed, train_fraction=runner.TRAIN_FRACTION):
        assert n == 6
        assert seed == 123
        assert train_fraction == runner.TRAIN_FRACTION
        return train_idx, eval_idx

    def fake_high_threshold(batch_z, batch_train_idx):
        np.testing.assert_allclose(batch_z, z)
        np.testing.assert_array_equal(batch_train_idx, train_idx)
        return 1.0

    def fake_label_truth(name, batch_z, *, high_energy_threshold):
        value = np.asarray(batch_z, dtype=np.float64)
        assert high_energy_threshold == 1.0
        if name == "latent_x_positive":
            return (value[:, 0] > 0.0).astype(np.float64)
        if name == "latent_y_positive":
            return (value[:, 1] > 0.0).astype(np.float64)
        if name == "high_energy":
            return (np.sum(np.square(value), axis=1) > 1.0).astype(np.float64)
        raise AssertionError(name)

    def fake_fit_probe(h_train, y_train):
        assert h_train.shape == (4, 2)
        assert not np.any(np.abs(h_train) == sentinel)
        return {"positive_rate": float(np.mean(y_train))}

    def fake_predict_probe(probe, h):
        value = np.asarray(h, dtype=np.float64)
        logits = value[:, 0] + 0.25 * value[:, 1] - float(probe["positive_rate"])
        probabilities = 1.0 / (1.0 + np.exp(-np.clip(logits, -60.0, 60.0)))
        return {
            "probabilities": probabilities,
            "logits": logits,
            "predictions": (probabilities >= 0.5).astype(np.float64),
        }

    def fake_run_experiment(**kwargs):
        assert kwargs["run_id"] == "gap-ledger-head-on-h-seed-123"
        return SimpleNamespace(
            run_id=kwargs["run_id"],
            source_spec={"name": "fixture-source"},
            classifier_spec={"name": "fixture-classifier"},
            metrics={
                "quality_q": 0.1,
                "quality_margin": 0.2,
                "linear_identifiability_r2": 0.3,
                "approx_identifiability_proxy": 0.4,
            },
            artifacts={
                "envelope": kwargs["envelope_artifact"],
                "report": kwargs["report_artifact"],
            },
        )

    monkeypatch.setattr(runner, "SAMPLE_COUNT", 6)
    monkeypatch.setattr(runner, "make_toy_batch", fake_batch)
    monkeypatch.setattr(runner.distinction, "_train_eval_split", fake_split)
    monkeypatch.setattr(runner.distinction, "_high_energy_threshold", fake_high_threshold)
    monkeypatch.setattr(runner.distinction, "_label_truth", fake_label_truth)
    monkeypatch.setattr(runner.distinction, "_fit_probe", fake_fit_probe)
    monkeypatch.setattr(runner.distinction, "_predict_probe", fake_predict_probe)
    monkeypatch.setattr(runner, "run_experiment", fake_run_experiment)
    return {"sentinel": sentinel, "train_idx": train_idx, "eval_idx": eval_idx}


def test_default_boundary_and_gap_channels():
    assert runner.SEED_COUNT >= 20
    assert runner.REPRESENTATION_BOUNDARY == "learned_h"
    assert runner.INFERENCE_NO_GROUND_TRUTH_Z is True
    assert runner.GAP_CHANNELS == (
        "prediction_error",
        "low_margin",
        "transition_unstable",
        "off_target_intervention",
    )
    assert set(runner.FORBIDDEN_INFERENCE_COLUMNS) == {
        "z",
        "z_pair",
        "gap_label",
        "prediction_error",
        "eval_gap_labels",
    }


def test_h_only_feature_builder_rejects_forbidden_columns():
    features, columns = runner._build_inference_features(
        h=np.ones((3, 2)),
        score=np.zeros((3, 3)),
        margin=np.ones((3, 3)),
        transition_delta=np.full((3, 3), 0.25),
        quality_scalars=np.array([0.1, 0.2, 0.3, 0.4]),
    )

    assert features.shape == (3, 15)
    assert columns == [
        "h:0",
        "h:1",
        "score:latent_x_positive",
        "score:latent_y_positive",
        "score:high_energy",
        "margin:latent_x_positive",
        "margin:latent_y_positive",
        "margin:high_energy",
        "transition_delta:latent_x_positive",
        "transition_delta:latent_y_positive",
        "transition_delta:high_energy",
        "quality:quality_q",
        "quality:quality_margin",
        "quality:linear_identifiability_r2",
        "quality:approx_identifiability_proxy",
    ]
    assert not any(column.split(":", 1)[0] in runner.FORBIDDEN_INFERENCE_COLUMNS for column in columns)

    with pytest.raises(ValueError, match="forbidden inference column"):
        runner._assert_inference_columns(["h:0", "z"])


def test_surface_uses_disjoint_split_and_four_gap_channels(monkeypatch):
    fixture = _record_fixture(monkeypatch)

    surface = runner._surface_for_seed(seed=123)

    assert surface["features"].shape == (6, 15)
    assert surface["gap_labels"].shape == (6, 4)
    np.testing.assert_array_equal(surface["train_idx"], fixture["train_idx"])
    np.testing.assert_array_equal(surface["eval_idx"], fixture["eval_idx"])
    assert set(surface["train_idx"].tolist()).isdisjoint(surface["eval_idx"].tolist())
    assert surface["feature_columns"] == runner._feature_columns(2)
    assert not np.any(np.abs(surface["features"]) == fixture["sentinel"])
    assert set(surface["gap_label_rates"]) == set(runner.GAP_CHANNELS)
    assert set(surface["eval_gap_label_rates"]) == set(runner.GAP_CHANNELS)


def test_run_record_wires_three_arms_same_eval_error_and_no_z_leak(monkeypatch):
    fixture = _record_fixture(monkeypatch)
    captured = {"fit": 0, "predict": 0}
    learned_probabilities = np.array([[0.9, 0.1, 0.2, 0.3], [0.1, 0.8, 0.7, 0.6]])

    def fake_fit_gap_head(features, labels):
        captured["fit"] += 1
        captured["fit_features"] = np.array(features, copy=True)
        captured["fit_labels"] = np.array(labels, copy=True)
        assert features.shape == (4, 15)
        assert labels.shape == (4, 4)
        assert not np.any(np.abs(features) == fixture["sentinel"])
        return {"heads": "fixture"}

    def fake_predict_gap_head(heads, features):
        captured["predict"] += 1
        captured["predict_features"] = np.array(features, copy=True)
        assert heads == {"heads": "fixture"}
        assert features.shape == (2, 15)
        assert not np.any(np.abs(features) == fixture["sentinel"])
        return learned_probabilities

    monkeypatch.setattr(runner, "_fit_gap_head", fake_fit_gap_head)
    monkeypatch.setattr(runner, "_predict_gap_head", fake_predict_gap_head)

    record = runner._run_record(seed=123, seed_index=7)

    assert captured["fit"] == 1
    assert captured["predict"] == 1
    assert record["split"]["overlap_count"] == 0
    assert record["representation_boundary"] == "learned_h"
    assert record["inference_no_ground_truth_z"] is True
    assert record["feature_columns"] == runner._feature_columns(2)
    assert record["forbidden_inference_columns"] == list(runner.FORBIDDEN_INFERENCE_COLUMNS)
    assert set(record["arms"]) == {"vanilla", "posthoc_report_only", "learned_gap_head_on_h"}
    assert record["arms"]["posthoc_report_only"]["inference"] is False
    vanilla = record["arms"]["vanilla"]
    posthoc = record["arms"]["posthoc_report_only"]["oracle_diagnostics"]
    learned = record["arms"]["learned_gap_head_on_h"]
    assert vanilla["prediction_error_rate"] == posthoc["prediction_error_rate"]
    assert vanilla["prediction_error_rate"] == learned["prediction_error_rate"]
    assert "unlogged_error_rate_delta_learned_minus_vanilla" in record["comparison"]


def test_posthoc_report_only_does_not_train(monkeypatch):
    calls = {"fit": 0}

    def fail_fit(*args, **kwargs):
        calls["fit"] += 1
        raise AssertionError("posthoc must not fit")

    monkeypatch.setattr(runner, "_fit_gap_head", fail_fit)
    labels = np.array([[1.0, 0.0, 1.0, 0.0], [0.0, 1.0, 0.0, 1.0]], dtype=np.float64)
    error = np.array([1.0, 0.0], dtype=np.float64)

    arm = runner._posthoc_report_only(eval_labels=labels, eval_error=error)

    assert calls["fit"] == 0
    assert arm["inference"] is False
    assert arm["eval_gap_label_rates"]["prediction_error"] == pytest.approx(0.5)
    assert arm["oracle_diagnostics"]["failure_detection_auroc"]["value"] == pytest.approx(1.0)


def test_payload_and_markdown_share_boundary_fields():
    record = {
        "seed": 1,
        "arms": {
            arm: {
                "failure_detection_auroc": {"value": 0.5},
                "ece": {"value": 0.1},
                "unlogged_error_rate": 0.2,
                "critical_unlogged_error_rate": 0.2,
                "prediction_error_rate": 0.3,
                "primary_gap_sound": {
                    "low_gap_implies_error_within_epsilon": 0.4,
                    "error_above_epsilon_implies_gap_at_least_tau": 0.5,
                },
            }
            for arm in ("vanilla", "learned_gap_head_on_h")
        },
        "comparison": {
            "unlogged_error_rate_delta_learned_minus_vanilla": -0.1,
            "critical_unlogged_error_rate_delta_learned_minus_vanilla": -0.1,
            "failure_detection_auroc_delta_learned_minus_vanilla": 0.0,
        },
    }

    payload = runner._payload([record])
    report = runner._render_report(payload)

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["representation_boundary"] == "learned_h"
    assert payload["inference_no_ground_truth_z"] is True
    assert payload["feature_columns"] == runner._feature_columns(2)
    assert payload["forbidden_inference_columns"] == list(runner.FORBIDDEN_INFERENCE_COLUMNS)
    assert "# Gap-Ledger Head on Learned h" in report
    assert "Representation boundary: `learned_h`" in report
    assert "Forbidden inference columns" in report


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(
        runner,
        "_records",
        lambda: [
            {
                "seed": 1,
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
                    for arm in ("vanilla", "learned_gap_head_on_h")
                },
                "comparison": {
                    "unlogged_error_rate_delta_learned_minus_vanilla": 0.0,
                    "critical_unlogged_error_rate_delta_learned_minus_vanilla": 0.0,
                    "failure_detection_auroc_delta_learned_minus_vanilla": 0.0,
                },
            }
        ],
    )

    runner.main()

    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["aggregate"]["record_count"] == 1
    assert payload["representation_boundary"] == "learned_h"
    assert payload["inference_no_ground_truth_z"] is True
    assert "# Gap-Ledger Head on Learned h" in report
