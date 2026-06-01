import json
import math
from types import SimpleNamespace

import numpy as np
import pytest

from scripts import run_gaussian_ou_gap_ledger_head as runner


def _install_record_fixture(monkeypatch):
    calls = []
    fit_order = []
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
    train_idx = np.array([1, 2, 3, 4], dtype=np.int64)
    eval_idx = np.array([0, 5], dtype=np.int64)

    expected_gap_labels = np.array(
        [
            [1.0, 0.0, 1.0, 1.0],
            [0.0, 0.0, 0.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
            [0.0, 0.0, 1.0, 1.0],
            [0.0, 1.0, 1.0, 1.0],
            [0.0, 1.0, 1.0, 1.0],
        ],
        dtype=np.float64,
    )

    def fake_make_toy_batch(sample_count, *, rho, seed):
        assert sample_count == 6
        assert rho == runner.RHO
        assert seed == 4242
        return SimpleNamespace(z=z, z_pair=z_pair)

    def fake_train_eval_split(n, *, seed, train_fraction=runner.TRAIN_FRACTION):
        assert n == 6
        assert seed == 4242
        assert train_fraction == runner.TRAIN_FRACTION
        return train_idx, eval_idx

    def fake_high_energy_threshold(batch_z, batch_train_idx):
        np.testing.assert_allclose(batch_z, z)
        np.testing.assert_array_equal(batch_train_idx, train_idx)
        return 1.0

    def fake_fit_probe(batch_z, labels):
        name = runner.DISTINCTIONS[len(fit_order)]
        fit_order.append((name, np.array(batch_z, copy=True), np.array(labels, copy=True)))
        return {"name": name}

    def fake_predict_probe(probe, batch_z):
        name = probe["name"]
        value = np.asarray(batch_z, dtype=np.float64)
        labels = runner.distinction._label_truth(name, value, high_energy_threshold=1.0)
        predictions = np.array(labels, copy=True)
        if name == "latent_x_positive":
            miss = (value[:, 0] > 1.5) & (value[:, 1] > 0.5)
            predictions[miss] = 0.0
        magnitude = np.where(np.max(np.abs(value), axis=1) < 0.5, 0.05, 2.0)
        logits = np.where(predictions > 0.5, magnitude, -magnitude).astype(np.float64)
        return {
            "probabilities": runner._sigmoid(logits),
            "logits": logits,
            "predictions": predictions.astype(np.float64),
        }

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return SimpleNamespace(
            run_id=kwargs["run_id"],
            source_spec={"name": "fixture-source", "sample_count": kwargs["sample_count"]},
            classifier_spec={"name": "fixture-classifier"},
            metrics={
                "quality_q": 0.25,
                "quality_margin": 0.75,
                "linear_identifiability_r2": 0.5,
                "approx_identifiability_proxy": 0.125,
            },
            artifacts={
                "envelope": kwargs["envelope_artifact"],
                "report": kwargs["report_artifact"],
            },
        )

    monkeypatch.setattr(runner, "SAMPLE_COUNT", 6)
    monkeypatch.setattr(runner, "make_toy_batch", fake_make_toy_batch)
    monkeypatch.setattr(runner, "run_experiment", fake_run_experiment)
    monkeypatch.setattr(runner.distinction, "_train_eval_split", fake_train_eval_split)
    monkeypatch.setattr(runner.distinction, "_high_energy_threshold", fake_high_energy_threshold)
    monkeypatch.setattr(runner.distinction, "_fit_probe", fake_fit_probe)
    monkeypatch.setattr(runner.distinction, "_predict_probe", fake_predict_probe)

    return {
        "calls": calls,
        "fit_order": fit_order,
        "train_idx": train_idx,
        "eval_idx": eval_idx,
        "expected_gap_labels": expected_gap_labels,
    }


def test_default_config_matches_structural_protocol_b():
    assert runner.SEED_COUNT >= 20
    assert runner.BETA == 1.0
    assert runner.PRIMARY_EPSILON == 0.0
    assert runner.PRIMARY_TAU == 0.5
    assert runner.GAP_CHANNELS == (
        "prediction_error",
        "low_margin",
        "transition_unstable",
        "off_target_intervention",
    )


def test_gap_head_probability_shape_and_bounds_on_separable_fixture():
    x = np.array([[-2.0], [-1.0], [1.0], [2.0]], dtype=np.float64)
    labels = np.array(
        [
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0],
            [1.0, 0.0, 1.0, 1.0],
            [1.0, 0.0, 1.0, 1.0],
        ],
        dtype=np.float64,
    )

    heads = runner._fit_gap_head(x, labels, steps=300, lr=0.25)
    probabilities = runner._predict_gap_head(heads, x)

    assert probabilities.shape == labels.shape
    assert np.all(probabilities >= 0.0)
    assert np.all(probabilities <= 1.0)
    assert probabilities[0, 0] < 0.2
    assert probabilities[-1, 0] > 0.8


def test_gap_loss_is_bce_plus_beta_unlogged_error_penalty():
    labels = np.array([[1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0]], dtype=np.float64)
    probabilities = np.array(
        [[0.25, 0.2, 0.1, 0.1], [0.75, 0.8, 0.1, 0.1]],
        dtype=np.float64,
    )
    prediction_error = np.array([1.0, 0.0], dtype=np.float64)

    loss = runner._gap_loss(labels, probabilities, prediction_error, beta=1.0)
    expected_bce = runner._binary_cross_entropy(labels.reshape(-1), probabilities.reshape(-1))

    assert loss["bce"] == pytest.approx(expected_bce)
    assert loss["unlogged_error_penalty"] == pytest.approx((1.0 - 0.25) / 2.0)
    assert loss["total"] == pytest.approx(expected_bce + (1.0 - 0.25) / 2.0)


def test_auroc_handles_perfect_reversed_and_degenerate_cases():
    labels = np.array([0.0, 0.0, 1.0, 1.0], dtype=np.float64)

    perfect = runner._auroc(labels, np.array([0.1, 0.2, 0.8, 0.9], dtype=np.float64))
    reversed_auc = runner._auroc(labels, np.array([0.9, 0.8, 0.2, 0.1], dtype=np.float64))
    constant_score = runner._auroc(labels, np.array([0.5, 0.5, 0.5, 0.5], dtype=np.float64))
    constant_label = runner._auroc(np.zeros(4), np.array([0.1, 0.2, 0.3, 0.4], dtype=np.float64))

    assert perfect == {"value": 1.0, "degenerate": False, "reason": "ok"}
    assert reversed_auc == {"value": 0.0, "degenerate": False, "reason": "ok"}
    assert constant_score == {"value": 0.5, "degenerate": True, "reason": "constant_score"}
    assert constant_label == {"value": 0.5, "degenerate": True, "reason": "constant_label"}


def test_ece_uses_fixed_bins_and_keeps_empty_bin_rows():
    labels = np.array([0.0, 1.0], dtype=np.float64)
    scores = np.array([0.1, 0.9], dtype=np.float64)

    ece = runner._ece(labels, scores, bins=5)

    assert ece["bins"] == 5
    assert len(ece["bin_rows"]) == 5
    assert ece["value"] == pytest.approx(0.1)
    assert ece["bin_rows"][2]["count"] == 0
    assert math.isnan(ece["bin_rows"][2]["confidence"])


def test_unlogged_error_and_gap_sound_primary_predicates():
    error = np.array([1.0, 1.0, 0.0, 0.0], dtype=np.float64)
    gap = np.array([0.2, 0.8, 0.1, 0.9], dtype=np.float64)

    assert runner._unlogged_error_rate(error, gap, tau=0.5) == pytest.approx(0.25)

    rows = runner._gap_sound_scan(error, gap)
    primary = runner._primary_gap_sound(rows)

    assert primary["tau"] == runner.PRIMARY_TAU
    assert primary["epsilon"] == runner.PRIMARY_EPSILON
    assert primary["low_gap_implies_error_within_epsilon"] == pytest.approx(0.5)
    assert primary["error_above_epsilon_implies_gap_at_least_tau"] == pytest.approx(0.5)


def test_features_and_labels_derives_gap_channels_and_canonical_projection(monkeypatch):
    fixture = _install_record_fixture(monkeypatch)

    data = runner._features_and_labels(seed=4242)

    assert fixture["calls"] == [
        {
            "use_torch": runner.USE_TORCH,
            "sample_count": 6,
            "seed": 4242,
            "rho": runner.RHO,
            "run_id": "gaussian-ou-gap-ledger-head-seed-4242",
            "envelope_artifact": runner.JSON_ARTIFACT,
            "report_artifact": runner.REPORT_ARTIFACT,
        }
    ]
    assert [name for name, _, _ in fixture["fit_order"]] == list(runner.DISTINCTIONS)
    assert data["features"].shape == (6, 19)
    np.testing.assert_array_equal(data["train_idx"], fixture["train_idx"])
    np.testing.assert_array_equal(data["eval_idx"], fixture["eval_idx"])
    np.testing.assert_array_equal(data["gap_labels"], fixture["expected_gap_labels"])
    np.testing.assert_array_equal(data["prediction_error"], [1.0, 0.0, 0.0, 0.0, 0.0, 0.0])
    assert data["margin_threshold"] == pytest.approx(1.805)
    assert data["label_rates"] == {
        "prediction_error": pytest.approx(1.0 / 6.0),
        "low_margin": pytest.approx(2.0 / 6.0),
        "transition_unstable": pytest.approx(4.0 / 6.0),
        "off_target_intervention": pytest.approx(5.0 / 6.0),
    }
    assert data["eval_label_rates"] == {
        "prediction_error": pytest.approx(0.5),
        "low_margin": pytest.approx(0.5),
        "transition_unstable": pytest.approx(1.0),
        "off_target_intervention": pytest.approx(1.0),
    }
    assert data["canonical_envelope_projection"] == {
        "run_id": "gaussian-ou-gap-ledger-head-seed-4242",
        "source_spec": {"name": "fixture-source", "sample_count": 6},
        "classifier_spec": {"name": "fixture-classifier"},
        "metrics": {
            "quality_q": 0.25,
            "quality_margin": 0.75,
            "linear_identifiability_r2": 0.5,
            "approx_identifiability_proxy": 0.125,
        },
        "artifacts": {
            "envelope": runner.JSON_ARTIFACT,
            "report": runner.REPORT_ARTIFACT,
        },
    }


def test_run_record_wires_gap_head_split_labels_and_eval_surface(monkeypatch):
    fixture = _install_record_fixture(monkeypatch)
    captured = {}
    eval_probabilities = np.array(
        [
            [0.9, 0.2, 0.3, 0.4],
            [0.1, 0.8, 0.2, 0.7],
        ],
        dtype=np.float64,
    )

    def fake_fit_gap_head(features, labels):
        captured["train_features"] = np.array(features, copy=True)
        captured["train_labels"] = np.array(labels, copy=True)
        return {"fixture": "gap-head"}

    def fake_predict_gap_head(heads, features):
        assert heads == {"fixture": "gap-head"}
        captured["eval_features"] = np.array(features, copy=True)
        return eval_probabilities

    monkeypatch.setattr(runner, "_fit_gap_head", fake_fit_gap_head)
    monkeypatch.setattr(runner, "_predict_gap_head", fake_predict_gap_head)

    record = runner._run_record(seed=4242, seed_index=3)

    assert fixture["calls"][0]["run_id"] == "gaussian-ou-gap-ledger-head-seed-4242"
    assert record["seed_index"] == 3
    assert record["seed_sequence_position"] == 4
    assert record["config"]["sample_count"] == 6
    assert record["config"]["train_count"] == 4
    assert record["config"]["eval_count"] == 2
    assert record["split"] == {
        "train_indices": [1, 2, 3, 4],
        "eval_indices": [0, 5],
        "overlap_count": 0,
    }
    assert set(record["split"]["train_indices"]).isdisjoint(record["split"]["eval_indices"])
    np.testing.assert_array_equal(
        captured["train_labels"], fixture["expected_gap_labels"][fixture["train_idx"]]
    )
    assert captured["train_features"].shape == (4, 19)
    assert captured["eval_features"].shape == (2, 19)
    assert record["gap_label_rates"] == {
        "prediction_error": pytest.approx(1.0 / 6.0),
        "low_margin": pytest.approx(2.0 / 6.0),
        "transition_unstable": pytest.approx(4.0 / 6.0),
        "off_target_intervention": pytest.approx(5.0 / 6.0),
    }
    assert record["eval_gap_label_rates"] == {
        "prediction_error": pytest.approx(0.5),
        "low_margin": pytest.approx(0.5),
        "transition_unstable": pytest.approx(1.0),
        "off_target_intervention": pytest.approx(1.0),
    }
    vanilla = record["arms"]["vanilla"]
    gap_head = record["arms"]["gap_head"]
    assert vanilla["prediction_error_rate"] == gap_head["prediction_error_rate"] == pytest.approx(0.5)
    assert vanilla["unlogged_error_rate"] == pytest.approx(0.5)
    assert gap_head["unlogged_error_rate"] == pytest.approx(0.0)
    assert gap_head["failure_detection_auroc"]["value"] == pytest.approx(1.0)
    assert record["comparison"]["unlogged_error_rate_delta_gap_minus_vanilla"] == pytest.approx(-0.5)
    assert record["comparison"]["failure_detection_auroc_delta_gap_minus_vanilla"] == pytest.approx(0.5)


def test_vanilla_vs_gap_head_metrics_are_assembled_on_same_error_surface():
    labels = np.array(
        [[1.0, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0], [0.0, 0.0, 1.0, 0.0]],
        dtype=np.float64,
    )
    error = np.array([1.0, 0.0, 0.0], dtype=np.float64)
    vanilla = np.zeros_like(labels)
    gap = np.array(
        [[0.9, 0.1, 0.1, 0.1], [0.1, 0.9, 0.1, 0.1], [0.1, 0.1, 0.9, 0.1]],
        dtype=np.float64,
    )

    vanilla_metrics = runner._metrics_for_arm(
        arm="vanilla", probabilities=vanilla, labels=labels, prediction_error=error
    )
    gap_metrics = runner._metrics_for_arm(
        arm="gap_head", probabilities=gap, labels=labels, prediction_error=error
    )

    assert vanilla_metrics["prediction_error_rate"] == gap_metrics["prediction_error_rate"]
    assert vanilla_metrics["unlogged_error_rate"] == pytest.approx(1.0 / 3.0)
    assert gap_metrics["unlogged_error_rate"] == pytest.approx(0.0)


def test_payload_contains_json_evidence_boundary_and_negative_result():
    record = {
        "seed": 1,
        "arms": {
            "vanilla": {
                "failure_detection_auroc": {"value": 0.5},
                "ece": {"value": 0.5},
                "unlogged_error_rate": 0.5,
                "critical_unlogged_error_rate": 0.5,
                "prediction_error_rate": 0.5,
                "gap_sound_scan": [
                    {
                        "tau": runner.PRIMARY_TAU,
                        "epsilon": runner.PRIMARY_EPSILON,
                        "low_gap_implies_error_within_epsilon": 0.5,
                        "error_above_epsilon_implies_gap_at_least_tau": 0.0,
                    }
                ],
            },
            "gap_head": {
                "failure_detection_auroc": {"value": 0.5},
                "ece": {"value": 0.4},
                "unlogged_error_rate": 0.4,
                "critical_unlogged_error_rate": 0.3,
                "prediction_error_rate": 0.5,
                "gap_sound_scan": [
                    {
                        "tau": runner.PRIMARY_TAU,
                        "epsilon": runner.PRIMARY_EPSILON,
                        "low_gap_implies_error_within_epsilon": 0.6,
                        "error_above_epsilon_implies_gap_at_least_tau": 0.2,
                    }
                ],
            },
        },
        "comparison": {
            "unlogged_error_rate_delta_gap_minus_vanilla": -0.1,
            "critical_unlogged_error_rate_delta_gap_minus_vanilla": -0.2,
            "failure_detection_auroc_delta_gap_minus_vanilla": 0.0,
        },
    }

    payload = runner._payload([record])
    report = runner._render_report(payload)

    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_gaussian_ou_gap_ledger_head.py"
    )
    assert payload["source_artifacts"]["distinction_head_runner"] == (
        "scripts/run_gaussian_ou_distinction_head.py"
    )
    assert payload["applicability_boundary"]["primary_epsilon"] == 0.0
    assert "approximately chance" in payload["negative_result_note"]
    assert "## Applicability Boundary" in report
    assert "## Negative Result Note" in report
    assert "UnloggedErrorRate" in report


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
                        "gap_sound_scan": [
                            {
                                "tau": runner.PRIMARY_TAU,
                                "epsilon": runner.PRIMARY_EPSILON,
                                "low_gap_implies_error_within_epsilon": 0.9,
                                "error_above_epsilon_implies_gap_at_least_tau": 0.8,
                            }
                        ],
                    }
                    for arm in ("vanilla", "gap_head")
                },
                "comparison": {
                    "unlogged_error_rate_delta_gap_minus_vanilla": 0.0,
                    "critical_unlogged_error_rate_delta_gap_minus_vanilla": 0.0,
                    "failure_detection_auroc_delta_gap_minus_vanilla": 0.0,
                },
            }
        ],
    )

    runner.main()

    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["aggregate"]["record_count"] == 1
    assert "# Gaussian-OU Gap-Ledger-Head Experiment" in report
    assert "Total records: `1`" in report


def test_non_finite_inputs_fail_closed():
    labels = np.array([[1.0, 0.0, 0.0, 0.0]], dtype=np.float64)
    probabilities = np.array([[float("nan"), 0.0, 0.0, 0.0]], dtype=np.float64)
    error = np.array([1.0], dtype=np.float64)

    with pytest.raises(ValueError, match="non-finite"):
        runner._gap_loss(labels, probabilities, error)


def test_does_not_mutate_schema_or_package_exports():
    import bedc_quality_lab
    from bedc_quality_lab.schema import SCHEMA_ID

    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert hasattr(bedc_quality_lab, "QualityEvidenceEnvelope")
    assert not hasattr(bedc_quality_lab, "GapLedgerHead")
