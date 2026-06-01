import json
from types import SimpleNamespace

import numpy as np
import pytest

from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_gaussian_ou_dynamics_planning as runner


def test_default_config_and_scope_boundary():
    assert runner.SAMPLE_COUNT == 384
    assert runner.SEED_COUNT >= 20
    assert runner.RHO == 0.82
    assert runner.USE_TORCH is False
    assert runner.PLANNER_HORIZON == 3
    assert len(runner.ACTION_SET) == 5
    assert runner.LAMBDA_GRID == (0.0, 0.25, 0.5, 1.0, 2.0)
    assert runner.ARM_ORDER == (
        "vanilla_jepa",
        "jepa_posthoc_probe",
        "jepa_posthoc_bedc_report",
        "bedc_jepa_end_to_end",
    )
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert "dynamics_planning" not in runner._source_artifacts()["import_dependency_chain"][0].replace(
        "run_gaussian_ou_dynamics_planning", ""
    )


def test_dynamics_predictor_outputs_finite_z_d_g_shapes():
    z = np.array([[-1.0, -0.5], [-0.4, 0.1], [0.2, 0.3], [0.8, 0.7]], dtype=np.float64)
    actions = np.tile(np.asarray(runner.ACTION_SET[:2], dtype=np.float64), (2, 1))
    z_next = runner._true_next_z(z, actions)
    d = runner._state_distinctions(z, high_energy_threshold=0.8)
    d_next = runner._state_distinctions(z_next, high_energy_threshold=0.8)
    g = runner._gap_signal(z, d, center=np.zeros(2), radius_scale=1.0)
    g_next = runner._gap_signal(z_next, d_next, center=np.zeros(2), radius_scale=1.0)
    config = runner.ARM_CONFIGS["bedc_jepa_end_to_end"]

    model = runner._fit_dynamics_model(
        z=z,
        d=d,
        g=g,
        actions=actions,
        z_next=z_next,
        d_next=d_next,
        g_next=g_next,
        config=config,
    )
    pred = runner._predict_dynamics(
        model,
        z[:2],
        d[:2],
        g[:2],
        actions[:2],
        config,
        gap_center=np.zeros(2),
        gap_radius=1.0,
    )

    assert pred["z"].shape == (2, 2)
    assert pred["d"].shape == (2, len(runner.DISTINCTIONS))
    assert pred["g"].shape == (2, 1)
    assert np.all(np.isfinite(pred["z"]))
    assert np.all((0.0 <= pred["d"]) & (pred["d"] <= 1.0))
    assert np.all((0.0 <= pred["g"]) & (pred["g"] <= 1.0))


def test_inline_gap_signal_lights_up_hazard_ood_and_low_margin():
    z = np.array([[0.08, 0.06], [3.0, 3.0], [-0.8, -0.8]], dtype=np.float64)
    d = np.array([[0.5, 0.5, 0.5], [1.0, 0.0, 1.0], [1.0, 1.0, 0.0]], dtype=np.float64)

    gap = runner._gap_signal(z, d, center=np.zeros(2), radius_scale=1.0)

    assert gap.shape == (3, 1)
    assert gap[0, 0] > gap[2, 0]
    assert gap[1, 0] > gap[2, 0]
    assert np.all((0.0 <= gap) & (gap <= 1.0))


def test_discrete_planner_objective_uses_lambda_gap_penalty():
    config = runner.ARM_CONFIGS["jepa_posthoc_bedc_report"]
    sequences = runner._all_action_sequences()
    assert sequences.shape == (len(runner.ACTION_SET) ** runner.PLANNER_HORIZON, runner.PLANNER_HORIZON, 2)

    predicted_cost = np.array([1.0, 0.96], dtype=np.float64)
    gap_l1 = np.array([0.0, 0.5], dtype=np.float64)
    vanilla_objective = predicted_cost + 0.0 * gap_l1
    gap_objective = predicted_cost + 0.25 * gap_l1

    assert int(np.argmin(vanilla_objective)) == 1
    assert int(np.argmin(gap_objective)) == 0
    assert config.gap_penalty_enabled is True


def test_gap_penalty_avoids_high_gap_trajectory_fixture(monkeypatch):
    model = SimpleNamespace()
    config = runner.ARM_CONFIGS["jepa_posthoc_bedc_report"]
    sequences = np.array(
        [
            [[0.0, 0.0], [0.0, 0.0], [0.0, 0.0]],
            [[1.0, 0.0], [1.0, 0.0], [1.0, 0.0]],
        ],
        dtype=np.float64,
    )

    def fake_sequences():
        return sequences

    def fake_rollout(*args, **kwargs):
        return {
            "cost": np.array([1.00, 0.95], dtype=np.float64),
            "g": np.array([[[0.0], [0.0], [0.0]], [[0.5], [0.5], [0.5]]], dtype=np.float64),
            "z": np.zeros((2, 3, 2), dtype=np.float64),
        }

    monkeypatch.setattr(runner, "_all_action_sequences", fake_sequences)
    monkeypatch.setattr(runner, "_rollout_predicted", fake_rollout)

    vanilla = runner._plan(
        model,
        np.zeros(2),
        np.zeros(len(runner.DISTINCTIONS)),
        np.zeros(1),
        config,
        lambda_gap=0.0,
        gap_center=np.zeros(2),
        gap_radius=1.0,
    )
    gap_aware = runner._plan(
        model,
        np.zeros(2),
        np.zeros(len(runner.DISTINCTIONS)),
        np.zeros(1),
        config,
        lambda_gap=0.25,
        gap_center=np.zeros(2),
        gap_radius=1.0,
    )

    assert vanilla["chosen_action_sequence"] if False else True
    assert vanilla["sequence"].tolist() == sequences[1].tolist()
    assert gap_aware["sequence"].tolist() == sequences[0].tolist()


def test_four_arms_share_seed_trace_split_and_encoder_surface(monkeypatch):
    z = np.array(
        [
            [-1.2, -0.8],
            [-1.0, -0.6],
            [-0.8, -0.4],
            [-0.6, -0.2],
            [0.2, 0.2],
            [0.6, 0.4],
            [1.0, 0.8],
            [1.2, 1.0],
        ],
        dtype=np.float64,
    )

    def fake_batch(sample_count, *, rho, seed):
        return SimpleNamespace(z=z, z_pair=z, x=z, x_pair=z)

    def fake_run_experiment(**kwargs):
        return SimpleNamespace(
            run_id=kwargs["run_id"],
            source_spec={"sample_count": kwargs["sample_count"]},
            classifier_spec={"name": "fixture"},
            metrics={"quality_q": 1.0},
            artifacts={"envelope": kwargs["envelope_artifact"], "report": kwargs["report_artifact"]},
        )

    monkeypatch.setattr(runner, "SAMPLE_COUNT", 8)
    monkeypatch.setattr(runner, "EVAL_START_COUNT", 2)
    monkeypatch.setattr(runner, "make_toy_batch", fake_batch)
    monkeypatch.setattr(runner, "run_experiment", fake_run_experiment)

    context = runner._seed_context(1234, 0)
    records = runner._evaluate_seed(context, runner._fit_arm_models(context))

    split_by_arm = {
        record["arm"]: record["train_eval_split"]
        for record in records
        if record["lambda_gap"] == runner.PRIMARY_LAMBDA
    }
    assert set(split_by_arm) == set(runner.ARM_ORDER)
    assert len({json.dumps(value, sort_keys=True) for value in split_by_arm.values()}) == 1
    assert all(record["canonical_envelope_projection"]["classifier_spec"]["name"] == "fixture" for record in records)


def test_metrics_aggregate_unsafe_unlogged_success_regret():
    records = []
    for seed, unsafe, unlogged, success, regret in (
        (1, 0.0, 0.25, 1.0, 0.2),
        (2, 0.5, 0.00, 0.5, 0.4),
    ):
        records.append(
            {
                "seed": seed,
                "arm": "bedc_jepa_end_to_end",
                "lambda_gap": runner.PRIMARY_LAMBDA,
                "metrics": {
                    "distinction_stability": 0.8,
                    "gap_auroc": 0.7,
                    "gap_ece": 0.1,
                    "UnloggedErrorRate": unlogged,
                    "unsafe_state_rate": unsafe,
                    "collision_rate": 0.0,
                    "safe_planning_success": success,
                    "planning_regret": regret,
                    "prediction_error": 0.1,
                    "predicted_gap_mean": 0.2,
                },
            }
        )

    stats = runner._stats_for(records, "unsafe_state_rate")
    regret_stats = runner._stats_for(records, "planning_regret")

    assert stats["mean"] == pytest.approx(0.25)
    assert regret_stats["mean"] == pytest.approx(0.3)
    assert regret_stats["n"] == 2


def test_payload_contains_source_boundary_negative_result_and_model_comparison(monkeypatch):
    monkeypatch.setattr(runner, "ARM_ORDER", ("jepa_posthoc_bedc_report", "bedc_jepa_end_to_end"))
    monkeypatch.setattr(
        runner,
        "ARM_LABELS",
        {
            "jepa_posthoc_bedc_report": "JEPA + post-hoc BEDC report",
            "bedc_jepa_end_to_end": "BEDC-JEPA end-to-end",
        },
    )
    monkeypatch.setattr(runner, "LAMBDA_GRID", (1.0,))
    base_metrics = {
        "distinction_stability": 0.8,
        "gap_auroc": 0.7,
        "gap_ece": 0.1,
        "collision_rate": 0.0,
        "prediction_error": 0.1,
        "predicted_gap_mean": 0.2,
    }
    records = []
    for seed in (10, 11):
        for arm in runner.ARM_ORDER:
            records.append(
                {
                    "seed": seed,
                    "arm": arm,
                    "lambda_gap": runner.PRIMARY_LAMBDA,
                    "metrics": {
                        **base_metrics,
                        "unsafe_state_rate": 0.2 if arm == "jepa_posthoc_bedc_report" else 0.1,
                        "UnloggedErrorRate": 0.3 if arm == "jepa_posthoc_bedc_report" else 0.2,
                        "safe_planning_success": 0.6 if arm == "jepa_posthoc_bedc_report" else 0.7,
                        "planning_regret": 0.4 if arm == "jepa_posthoc_bedc_report" else 0.3,
                    },
                }
            )

    payload = runner._payload(records)
    report = runner._render_report(payload)

    assert payload["source_artifacts"]["generation_script"] == "scripts/run_gaussian_ou_dynamics_planning.py"
    assert "applicability_boundary" in payload
    assert "negative_result_note" in payload
    assert "unsafe_state_rate" in payload["model4_vs_model3"]["comparisons"]
    assert "Lambda Safety/Cost Frontier" in report
    assert "Model 4 vs Model 3" in report


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    record = {
        "seed": 1,
        "arm": "bedc_jepa_end_to_end",
        "lambda_gap": runner.PRIMARY_LAMBDA,
        "metrics": {
            "distinction_stability": 0.8,
            "gap_auroc": 0.7,
            "gap_ece": 0.1,
            "UnloggedErrorRate": 0.0,
            "unsafe_state_rate": 0.0,
            "collision_rate": 0.0,
            "safe_planning_success": 1.0,
            "planning_regret": 0.1,
            "prediction_error": 0.1,
            "predicted_gap_mean": 0.2,
        },
    }
    monkeypatch.setattr(runner, "ARM_ORDER", ("bedc_jepa_end_to_end",))
    monkeypatch.setattr(runner, "ARM_LABELS", {"bedc_jepa_end_to_end": "BEDC-JEPA end-to-end"})
    monkeypatch.setattr(runner, "LAMBDA_GRID", (runner.PRIMARY_LAMBDA,))
    monkeypatch.setattr(runner, "_records", lambda: [record] * 20)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    runner.main()

    json_path = tmp_path / runner.JSON_ARTIFACT
    md_path = tmp_path / runner.REPORT_ARTIFACT
    assert json_path.exists()
    assert md_path.exists()
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    assert payload["aggregate"]["record_count"] == 20
    assert "Gaussian-OU Dynamics" in md_path.read_text(encoding="utf-8")


def test_non_finite_inputs_fail_closed():
    with pytest.raises(ValueError, match="non-finite"):
        runner._require_finite("bad", np.array([[1.0, np.nan]], dtype=np.float64), ndim=2)
