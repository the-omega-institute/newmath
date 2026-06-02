import math
import json
from types import SimpleNamespace

import numpy as np
import pytest

from scripts import run_gaussian_ou_distinction_head as runner


def fixture_record(seed=10, accuracy=1.0, bce=0.01):
    return {
        "seed": seed,
        "per_distinction": {
            name: {
                "train": {"accuracy": accuracy, "bce": bce},
                "eval": {"accuracy": accuracy, "bce": bce},
                "stability": 0.08,
                "margin": 4.0,
                "margin_distribution": {
                    "absolute_margin_mean": 4.0,
                    "absolute_margin_p10": 2.5,
                    "threshold_debt_rate": 0.0,
                },
                "generalization_gap": 0.0,
                "train_loss_components": {
                    "task_bce": bce,
                    "stability": 0.03,
                    "margin": 0.0,
                    "intervention": 0.12,
                    "objective_total": bce + 0.15 * 0.03 + 0.20 * 0.12,
                },
                "eval_loss_components": {
                    "task_bce": bce,
                    "stability": 0.08,
                    "margin": 0.0,
                    "intervention": 0.14,
                    "objective_total": bce + 0.15 * 0.08 + 0.20 * 0.14,
                },
            }
            for name in runner.DISTINCTIONS
        },
        "intervention": {
            name: {
                "on_target_flip_rate": 1.0,
                "on_target_truth_flip_rate": 1.0,
                "on_target_prediction_truth_flip_gap": 0.0,
                "off_target_flip_rate": 0.0,
            }
            for name in runner.DISTINCTIONS
        },
    }


def negative_result_record(
    *,
    distinction="latent_x_positive",
    eval_accuracy=1.0,
    generalization_gap=0.0,
    on_target_prediction_flip_rate=1.0,
    on_target_truth_flip_rate=1.0,
    off_target_flip_rate=0.0,
    threshold_debt_rate=0.0,
    absolute_margin_p10=2.5,
):
    record = fixture_record()
    row = record["per_distinction"][distinction]
    row["eval"]["accuracy"] = eval_accuracy
    row["generalization_gap"] = generalization_gap
    row["margin_distribution"]["threshold_debt_rate"] = threshold_debt_rate
    row["margin_distribution"]["absolute_margin_p10"] = absolute_margin_p10
    intervention = record["intervention"][distinction]
    intervention["on_target_flip_rate"] = on_target_prediction_flip_rate
    intervention["on_target_truth_flip_rate"] = on_target_truth_flip_rate
    intervention["on_target_prediction_truth_flip_gap"] = (
        on_target_prediction_flip_rate - on_target_truth_flip_rate
    )
    intervention["off_target_flip_rate"] = off_target_flip_rate
    return record


def test_default_config_is_structural_consensus_scope():
    assert runner.SAMPLE_COUNT == 384
    assert runner.SEED_COUNT == 30
    assert runner.RHO == 0.82
    assert runner.USE_TORCH is False
    assert runner.LOSS_WEIGHTS == {
        "task": 1.0,
        "stability": 0.15,
        "margin": 0.05,
        "intervention": 0.20,
    }
    assert runner.DISTINCTIONS == (
        "latent_x_positive",
        "latent_y_positive",
        "high_energy",
    )


def test_label_truth_uses_three_operational_per_sample_distinctions():
    z = np.array([[1.0, -2.0], [-0.5, 0.25], [0.0, 3.0]], dtype=np.float64)

    x_label = runner._label_truth("latent_x_positive", z, high_energy_threshold=1.0)
    y_label = runner._label_truth("latent_y_positive", z, high_energy_threshold=1.0)
    e_label = runner._label_truth("high_energy", z, high_energy_threshold=4.0)

    assert x_label.tolist() == [1.0, 0.0, 0.0]
    assert y_label.tolist() == [0.0, 1.0, 1.0]
    assert e_label.tolist() == [1.0, 0.0, 1.0]


def test_train_eval_split_is_deterministic_and_disjoint():
    train_a, eval_a = runner._train_eval_split(20, seed=123)
    train_b, eval_b = runner._train_eval_split(20, seed=123)
    train_c, eval_c = runner._train_eval_split(20, seed=124)

    assert train_a.tolist() == train_b.tolist()
    assert eval_a.tolist() == eval_b.tolist()
    assert set(train_a).isdisjoint(set(eval_a))
    assert len(train_a) == 14
    assert len(eval_a) == 6
    assert train_a.tolist() != train_c.tolist() or eval_a.tolist() != eval_c.tolist()


def test_run_record_passes_canonical_runner_arguments_and_builds_distinction_rows(monkeypatch):
    calls = []
    z = np.array(
        [
            [2.0, -1.0],
            [-2.0, -1.0],
            [2.0, 1.0],
            [-2.0, 1.0],
            [1.0, -2.0],
            [-1.0, -2.0],
            [1.0, 2.0],
            [-1.0, 2.0],
        ],
        dtype=np.float64,
    )
    z_pair = np.array(
        [
            [-2.0, -1.0],
            [-2.0, -1.0],
            [2.0, 1.0],
            [2.0, 1.0],
            [1.0, -2.0],
            [-1.0, -2.0],
            [1.0, 2.0],
            [-1.0, 2.0],
        ],
        dtype=np.float64,
    )

    def fake_make_toy_batch(sample_count, *, rho, seed):
        assert sample_count == 8
        assert rho == runner.RHO
        assert seed == 4242
        return SimpleNamespace(z=z, z_pair=z_pair)

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return SimpleNamespace(
            run_id=kwargs["run_id"],
            source_spec={"name": "fixture-source", "sample_count": kwargs["sample_count"]},
            classifier_spec={"name": "fixture-classifier"},
            metrics={"quality_q": 0.25, "quality_margin": 0.75},
            artifacts={
                "envelope": kwargs["envelope_artifact"],
                "report": kwargs["report_artifact"],
            },
        )

    monkeypatch.setattr(runner, "SAMPLE_COUNT", 8)
    monkeypatch.setattr(runner, "make_toy_batch", fake_make_toy_batch)
    monkeypatch.setattr(runner, "run_experiment", fake_run_experiment)

    record = runner._run_record(seed=4242, seed_index=2)

    assert calls == [
        {
            "use_torch": runner.USE_TORCH,
            "sample_count": 8,
            "seed": 4242,
            "rho": runner.RHO,
            "run_id": "gaussian-ou-distinction-head-seed-4242",
            "envelope_artifact": runner.JSON_ARTIFACT,
            "report_artifact": runner.REPORT_ARTIFACT,
        }
    ]
    assert record["seed_index"] == 2
    assert record["seed_sequence_position"] == 3
    assert record["run_id"] == "gaussian-ou-distinction-head-seed-4242"
    assert record["config"]["train_count"] == 6
    assert record["config"]["eval_count"] == 2
    assert record["config"]["high_energy_threshold"] == pytest.approx(5.0)
    assert record["split"] == {
        "train_indices": [1, 2, 4, 5, 6, 7],
        "eval_indices": [0, 3],
        "overlap_count": 0,
    }
    assert record["canonical_envelope_projection"] == {
        "run_id": "gaussian-ou-distinction-head-seed-4242",
        "source_spec": {"name": "fixture-source", "sample_count": 8},
        "classifier_spec": {"name": "fixture-classifier"},
        "metrics": {"quality_q": 0.25, "quality_margin": 0.75},
        "artifacts": {
            "envelope": runner.JSON_ARTIFACT,
            "report": runner.REPORT_ARTIFACT,
        },
    }

    x_row = record["per_distinction"]["latent_x_positive"]
    assert x_row["truth"]["label_positive_rate_train"] == pytest.approx(0.5)
    assert x_row["truth"]["label_positive_rate_eval"] == pytest.approx(0.5)
    assert x_row["truth"]["pair_label_positive_rate"] == pytest.approx(0.5)
    assert x_row["truth"]["ou_pair_truth_agreement_rate"] == pytest.approx(0.75)
    assert x_row["train"]["accuracy"] == pytest.approx(1.0)
    assert x_row["eval"]["accuracy"] == pytest.approx(1.0)
    assert 0.0 <= x_row["stability"] <= 1.0
    assert set(x_row["train_loss_components"]) == {
        "task_bce",
        "stability",
        "margin",
        "intervention",
        "objective_total",
    }
    assert set(x_row["eval_loss_components"]) == set(x_row["train_loss_components"])
    assert "threshold_debt_rate" in x_row["margin_distribution"]
    assert x_row["generalization_gap"] == pytest.approx(0.0)

    y_row = record["per_distinction"]["latent_y_positive"]
    assert y_row["truth"]["label_positive_rate_eval"] == pytest.approx(0.5)
    assert y_row["eval"]["accuracy"] == pytest.approx(1.0)
    assert 0.0 <= y_row["stability"] <= 1.0

    energy_row = record["per_distinction"]["high_energy"]
    assert energy_row["truth"]["label_positive_rate_train"] == pytest.approx(0.0)
    assert energy_row["truth"]["label_positive_rate_eval"] == pytest.approx(0.0)
    assert energy_row["truth"]["pair_label_positive_rate"] == pytest.approx(0.0)
    assert energy_row["eval"]["prediction_positive_rate"] == pytest.approx(0.0)

    assert record["intervention"]["latent_x_positive"]["on_target_flip_rate"] == pytest.approx(1.0)
    assert record["intervention"]["latent_x_positive"]["off_target_flip_rate"] == pytest.approx(0.0)
    assert record["intervention"]["latent_x_positive"]["per_distinction"]["latent_y_positive"] == {
        "prediction_flip_rate": 0.0,
        "truth_flip_rate": 0.0,
        "prediction_truth_flip_gap": 0.0,
        "post_intervention_truth_positive_rate": 0.5,
        "post_intervention_accuracy": 1.0,
    }
    assert record["intervention"]["latent_y_positive"]["on_target_flip_rate"] == pytest.approx(1.0)
    assert record["intervention"]["high_energy"]["on_target_flip_rate"] == pytest.approx(0.0)
    assert record["intervention"]["high_energy"]["on_target_truth_flip_rate"] == pytest.approx(1.0)
    assert record["intervention"]["high_energy"]["off_target_flip_rate"] == pytest.approx(0.0)


def test_probe_training_interface_learns_separable_fixture():
    x = np.array([[-2.0, 0.0], [-1.0, 0.2], [1.0, -0.1], [2.0, 0.3]], dtype=np.float64)
    y = np.array([0.0, 0.0, 1.0, 1.0], dtype=np.float64)

    probe = runner._fit_probe(x, y, steps=300, lr=0.25)
    metrics = runner._classification_metrics(probe, x, y)

    assert set(probe) == {"weights", "bias", "standardizer"}
    assert metrics["accuracy"] == pytest.approx(1.0)
    assert metrics["bce"] < 0.2
    assert metrics["margin"] > 1.0


def test_stability_intervention_and_loss_helpers_share_runner_semantics():
    z = np.array([[2.0, 0.5], [-2.0, -0.5], [0.4, 0.2], [-0.4, -0.2]], dtype=np.float64)
    z_pair = np.array([[0.2, 0.1], [0.3, -0.2], [2.0, 2.0], [-2.0, -2.0]], dtype=np.float64)
    y = runner._label_truth("latent_x_positive", z, high_energy_threshold=1.0)
    stable_views = runner._stability_views("latent_x_positive", z, high_energy_threshold=1.0)
    intervention_view, off_target_views = runner._intervention_training_views(
        "latent_x_positive", z, z_pair, high_energy_threshold=1.0
    )

    probe = runner._fit_probe(
        z,
        y,
        steps=120,
        lr=0.20,
        stable_views=stable_views,
        intervention_view=intervention_view,
        off_target_views=off_target_views,
    )
    losses = runner._loss_components(
        probe,
        z,
        y,
        stable_views=stable_views,
        intervention_view=intervention_view,
        off_target_views=off_target_views,
    )
    stability = runner._stability_metric(probe, z, stable_views=stable_views)

    assert len(stable_views) == len(runner._STABILITY_TRANSFORMS)
    assert all("truth_preserving_rate" in view for view in stable_views)
    assert losses["task_bce"] >= 0.0
    assert losses["objective_total"] == pytest.approx(
        runner.LOSS_WEIGHTS["task"] * losses["task_bce"]
        + runner.LOSS_WEIGHTS["stability"] * losses["stability"]
        + runner.LOSS_WEIGHTS["margin"] * losses["margin"]
        + runner.LOSS_WEIGHTS["intervention"] * losses["intervention"]
    )
    assert 0.0 <= stability["e_alpha_abs_probability_delta"] <= 1.0


def test_view_losses_change_probe_training_outcome():
    z = np.array(
        [
            [-2.0, -0.7],
            [-1.4, 0.2],
            [-0.8, 0.9],
            [-0.35, -0.4],
            [0.35, 0.4],
            [0.8, -0.9],
            [1.4, -0.2],
            [2.0, 0.7],
        ],
        dtype=np.float64,
    )
    z_pair = np.array(
        [
            [2.0, -0.7],
            [1.4, 0.2],
            [0.8, 0.9],
            [0.35, -0.4],
            [-0.35, 0.4],
            [-0.8, -0.9],
            [-1.4, -0.2],
            [-2.0, 0.7],
        ],
        dtype=np.float64,
    )
    y = runner._label_truth("latent_x_positive", z, high_energy_threshold=1.0)
    stable_views = runner._stability_views("latent_x_positive", z, high_energy_threshold=1.0)
    intervention_view, off_target_views = runner._intervention_training_views(
        "latent_x_positive", z, z_pair, high_energy_threshold=1.0
    )

    task_only = runner._fit_probe(z, y, steps=200, lr=0.20)
    with_view_losses = runner._fit_probe(
        z,
        y,
        steps=200,
        lr=0.20,
        stable_views=stable_views,
        intervention_view=intervention_view,
        off_target_views=off_target_views,
    )

    task_only_losses = runner._loss_components(
        task_only,
        z,
        y,
        stable_views=stable_views,
        intervention_view=intervention_view,
        off_target_views=off_target_views,
    )
    with_view_losses_components = runner._loss_components(
        with_view_losses,
        z,
        y,
        stable_views=stable_views,
        intervention_view=intervention_view,
        off_target_views=off_target_views,
    )
    task_only_probs = runner._predict_probe(task_only, z)["probabilities"]
    task_only_intervention_probs = runner._predict_probe(task_only, intervention_view["x"])[
        "probabilities"
    ]
    with_view_probs = runner._predict_probe(with_view_losses, z)["probabilities"]
    with_view_intervention_probs = runner._predict_probe(with_view_losses, intervention_view["x"])[
        "probabilities"
    ]
    task_only_on_target_agreement = float(
        np.mean(1.0 - np.abs(task_only_intervention_probs - (1.0 - task_only_probs)))
    )
    with_view_on_target_agreement = float(
        np.mean(1.0 - np.abs(with_view_intervention_probs - (1.0 - with_view_probs)))
    )

    assert task_only_losses["stability"] > 0.0
    assert task_only_losses["intervention"] > 0.0
    assert with_view_losses_components["stability"] < task_only_losses["stability"]
    assert with_view_losses_components["intervention"] < task_only_losses["intervention"]
    assert with_view_on_target_agreement > task_only_on_target_agreement


def test_stability_transform_coordinates_and_truth_preserving_masks():
    z = np.array(
        [
            [-0.04, 0.0],
            [0.04, 0.0],
            [0.01, 1.0],
            [-0.01, -1.0],
            [1.0, 0.5],
            [-1.0, -0.5],
        ],
        dtype=np.float64,
    )

    translated = runner._transform_latents(
        z, {"kind": "translate", "delta": (0.08, -0.06)}
    )
    rotated = runner._transform_latents(z, {"kind": "rotate", "radians": 0.08})
    bounded_noise = runner._transform_latents(z, {"kind": "noise", "scale": 0.035})
    axis_scaled = runner._transform_latents(
        z, {"kind": "scale_axis", "axis": 0, "scale": 0.86}
    )

    c = math.cos(0.08)
    s = math.sin(0.08)
    row_phase = np.arange(z.shape[0], dtype=np.float64).reshape(-1, 1)
    bounded = np.sin(z[:, ::-1] * 1.7 + row_phase * 0.37)
    expected_axis_scaled = np.array(z, copy=True)
    expected_axis_scaled[:, 0] *= 0.86

    assert np.allclose(translated, z + np.array([[0.08, -0.06]], dtype=np.float64))
    assert np.allclose(rotated, z @ np.array([[c, -s], [s, c]], dtype=np.float64).T)
    assert np.allclose(bounded_noise, z + 0.035 * bounded)
    assert np.allclose(axis_scaled, expected_axis_scaled)

    views = {
        view["name"]: view
        for view in runner._stability_views(
            "latent_x_positive", z, high_energy_threshold=10.0
        )
    }

    assert views["translate_small"]["mask"].tolist() == [
        False,
        True,
        True,
        False,
        True,
        True,
    ]
    assert views["rotate_small"]["mask"].tolist() == [
        True,
        True,
        False,
        False,
        True,
        True,
    ]
    assert views["noise_bounded"]["mask"].tolist() == [True] * 6
    assert views["occlude_x_soft"]["mask"].tolist() == [True] * 6
    assert views["occlude_y_soft"]["mask"].tolist() == [True] * 6
    assert views["translate_small"]["truth_preserving_rate"] == pytest.approx(4.0 / 6.0)
    assert views["rotate_small"]["truth_preserving_rate"] == pytest.approx(4.0 / 6.0)
    assert views["noise_bounded"]["truth_preserving_rate"] == pytest.approx(1.0)
    assert views["occlude_x_soft"]["truth_preserving_rate"] == pytest.approx(1.0)
    assert views["occlude_y_soft"]["truth_preserving_rate"] == pytest.approx(1.0)


def test_metrics_and_payload_aggregate_bce_stability_margin_and_gap(monkeypatch):
    monkeypatch.setattr(runner, "DISTINCTIONS", ("latent_x_positive", "latent_y_positive"))
    records = []
    for index, seed in enumerate((10, 11)):
        records.append(
                {
                    "seed": seed,
                    "per_distinction": {
                        "latent_x_positive": {
                            "train": {"accuracy": 0.95 + index * 0.02, "bce": 0.1},
                            "eval": {"accuracy": 0.9 + index * 0.02, "bce": 0.2},
                            "stability": 0.8,
                            "margin": 1.5,
                            "margin_distribution": {
                                "absolute_margin_mean": 1.5,
                                "absolute_margin_p10": 0.7,
                                "threshold_debt_rate": 0.1,
                            },
                            "generalization_gap": 0.03,
                            "train_loss_components": {
                                "task_bce": 0.1,
                                "stability": 0.2,
                                "margin": 0.3,
                                "intervention": 0.4,
                                "objective_total": 0.225,
                            },
                            "eval_loss_components": {
                                "task_bce": 0.2,
                                "stability": 0.3,
                                "margin": 0.4,
                                "intervention": 0.5,
                                "objective_total": 0.365,
                            },
                        },
                        "latent_y_positive": {
                            "train": {"accuracy": 0.76 + index * 0.02, "bce": 0.3},
                            "eval": {"accuracy": 0.7 + index * 0.02, "bce": 0.4},
                            "stability": 0.75,
                            "margin": 1.1,
                            "margin_distribution": {
                                "absolute_margin_mean": 1.1,
                                "absolute_margin_p10": 0.5,
                                "threshold_debt_rate": 0.2,
                            },
                            "generalization_gap": 0.04,
                            "train_loss_components": {
                                "task_bce": 0.3,
                                "stability": 0.2,
                                "margin": 0.3,
                                "intervention": 0.4,
                                "objective_total": 0.425,
                            },
                            "eval_loss_components": {
                                "task_bce": 0.4,
                                "stability": 0.3,
                                "margin": 0.4,
                                "intervention": 0.5,
                                "objective_total": 0.565,
                            },
                        },
                    },
                    "intervention": {
                        "latent_x_positive": {
                            "on_target_flip_rate": 0.95,
                            "on_target_truth_flip_rate": 1.0,
                            "on_target_prediction_truth_flip_gap": -0.05,
                            "off_target_flip_rate": 0.05,
                        },
                        "latent_y_positive": {
                            "on_target_flip_rate": 0.90,
                            "on_target_truth_flip_rate": 1.0,
                            "on_target_prediction_truth_flip_gap": -0.10,
                            "off_target_flip_rate": 0.10,
                        },
                    },
            }
        )

    payload = runner._payload(records)

    assert payload["aggregate"]["record_count"] == 2
    x_stats = payload["aggregate"]["per_distinction"]["latent_x_positive"]
    assert x_stats["eval_accuracy"]["mean"] == pytest.approx(0.91)
    assert x_stats["train_accuracy"]["mean"] == pytest.approx(0.96)
    assert x_stats["eval_bce"]["mean"] == pytest.approx(0.2)
    assert x_stats["stability"]["mean"] == pytest.approx(0.8)
    assert x_stats["margin"]["mean"] == pytest.approx(1.5)
    assert x_stats["eval_loss_components"]["objective_total"]["mean"] == pytest.approx(0.365)
    assert x_stats["generalization_gap"]["mean"] == pytest.approx(0.03)
    assert x_stats["intervention_separation"]["mean"] == pytest.approx(0.90)


def test_intervention_flips_target_and_bounds_off_target_fixture():
    z = np.array([[1.0, 2.0], [-1.5, 1.0], [2.0, -0.5]], dtype=np.float64)
    z_pair = np.array([[0.2, 0.1], [0.1, 0.1], [0.3, -0.2]], dtype=np.float64)

    flipped_x = runner._intervene("latent_x_positive", z, z_pair)
    flipped_y = runner._intervene("latent_y_positive", z, z_pair)
    paired = runner._intervene("high_energy", z, z_pair)
    crossed = runner._intervene("high_energy", z, z_pair, high_energy_threshold=1.0)

    assert runner._label_truth("latent_x_positive", flipped_x, high_energy_threshold=1.0).tolist() == [
        0.0,
        1.0,
        0.0,
    ]
    assert runner._label_truth("latent_y_positive", flipped_x, high_energy_threshold=1.0).tolist() == [
        1.0,
        1.0,
        0.0,
    ]
    assert runner._label_truth("latent_y_positive", flipped_y, high_energy_threshold=1.0).tolist() == [
        0.0,
        0.0,
        1.0,
    ]
    assert np.allclose(paired, z_pair)
    assert runner._label_truth("high_energy", crossed, high_energy_threshold=1.0).tolist() == [
        0.0,
        0.0,
        0.0,
    ]


def test_payload_contains_boundary_source_and_negative_result_fields():
    payload = runner._payload([fixture_record()])
    report = runner._render_report(payload)

    assert payload["config"]["loss_weights"] == runner.LOSS_WEIGHTS
    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_gaussian_ou_distinction_head.py"
    )
    assert payload["source_artifacts"]["canonical_runner"].endswith("run_experiment")
    assert "applicability_boundary" in payload
    assert "negative_result_note" in payload
    assert "deterministic fallback projection" in payload["applicability_boundary"][
        "representation_boundary"
    ]
    assert "## Applicability Boundary" in report
    assert "## Intervention Metrics" in report
    assert "## Loss Components" in report
    assert "## Margin Distribution" in report
    assert "## Negative Result Note" in report


def test_negative_result_findings_empty_for_high_accuracy_sensitive_record():
    aggregate = runner._aggregate([fixture_record()])

    assert runner._negative_result_findings(aggregate) == []


def test_negative_result_findings_emit_intervention_insensitive_payload():
    record = negative_result_record(
        on_target_prediction_flip_rate=0.49,
        on_target_truth_flip_rate=0.80,
        off_target_flip_rate=0.07,
    )
    aggregate = runner._aggregate([record])

    assert runner._negative_result_findings(aggregate) == [
        {
            "distinction": "latent_x_positive",
            "finding": "intervention_insensitive",
            "eval_accuracy_mean": 1.0,
            "on_target_truth_flip_rate_mean": 0.80,
            "on_target_prediction_flip_rate_mean": 0.49,
            "off_target_drift_mean": 0.07,
        }
    ]


def test_negative_result_findings_emit_held_out_accuracy_weak_payload():
    record = negative_result_record(
        eval_accuracy=0.69,
        generalization_gap=0.12,
    )
    aggregate = runner._aggregate([record])

    assert runner._negative_result_findings(aggregate) == [
        {
            "distinction": "latent_x_positive",
            "finding": "held_out_accuracy_weak",
            "eval_accuracy_mean": 0.69,
            "generalization_gap_mean": 0.12,
        }
    ]


def test_negative_result_findings_emit_threshold_debt_high_payload():
    record = negative_result_record(
        threshold_debt_rate=0.26,
        absolute_margin_p10=0.19,
    )
    aggregate = runner._aggregate([record])

    assert runner._negative_result_findings(aggregate) == [
        {
            "distinction": "latent_x_positive",
            "finding": "threshold_debt_high",
            "threshold_debt_rate_mean": 0.26,
            "absolute_margin_p10_mean": 0.19,
        }
    ]


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(
        runner,
        "_records",
        lambda: [fixture_record()],
    )

    runner.main()

    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["aggregate"]["record_count"] == 1
    assert "# Gaussian-OU Distinction-Head Experiment" in report
    assert "Total records: `1`" in report


def test_non_finite_input_fails_closed():
    bad = np.array([[1.0, 0.0], [math_nan(), 1.0]], dtype=np.float64)

    with pytest.raises(ValueError, match="non-finite"):
        runner._label_truth("latent_x_positive", bad, high_energy_threshold=1.0)


def test_does_not_mutate_schema_or_package_exports():
    import bedc_quality_lab
    from bedc_quality_lab.schema import SCHEMA_ID

    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert hasattr(bedc_quality_lab, "QualityEvidenceEnvelope")


def math_nan():
    return float("nan")
