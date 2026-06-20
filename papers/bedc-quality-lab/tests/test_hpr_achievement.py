import json
import subprocess
import sys

import pytest

from scripts import run_hpr_achievement as runner


def small_config(**overrides):
    values = {
        "sample_count": 96,
        "seed": 1717,
        "seed_count": 5,
        "train_fraction": 0.5,
        "observation_noise": 0.05,
        "logistic_epochs": 120,
        "learning_rate": 0.8,
        "l2_penalty": 0.001,
        "min_endpoint_auc": 0.95,
        "max_fake_action_auc": 0.62,
        "min_endpoint_fake_auc_gap_ci_low": 0.25,
    }
    values.update(overrides)
    return runner.HPRAchievementConfig(**values)


def test_run_benchmark_returns_json_compatible_learned_auc_contract():
    payload = runner.run_benchmark(small_config())
    reparsed = json.loads(json.dumps(payload, sort_keys=True))

    assert reparsed == payload
    assert payload["schema_id"] == runner.SCHEMA_ID
    assert payload["artifact_id"] == runner.ARTIFACT_ID
    assert payload["sample_summary"]["fake_action_source"] == "fresh_independent_rademacher"
    assert payload["model"]["learner"] == "deterministic_logistic_regression"
    assert payload["model"]["heldout_metric"] == "auc"
    assert payload["hardgate"]["status"] == "pass"
    assert payload["hardgate"]["confound_resistant"] is True
    assert payload["metrics"]["arms"]["endpoint"]["heldout_auc"]["ci95_low"] >= 0.95


def test_fake_action_is_independent_negative_control_and_hardgate_input():
    payload = runner.run_benchmark(small_config(seed=2001))
    fake_auc = payload["metrics"]["arms"]["fake_action"]["heldout_auc"]
    gap = payload["metrics"]["paired_differences"]["endpoint_minus_fake_action_auc"]

    assert payload["controls"]["fake_action"]["role"] == "negative_control"
    assert payload["controls"]["fake_action"]["source"] == "fresh_independent_rademacher"
    assert payload["controls"]["fake_action"]["status"] == "pass"
    assert fake_auc["mean"] <= payload["controls"]["fake_action"]["max_allowed_mean"]
    assert gap["ci95_low"] >= payload["hardgate"]["gates"]["endpoint_fake_action_auc_gap"]["min_allowed"]
    assert payload["hardgate"]["gates"]["fake_action_negative_control"]["metric"].endswith(
        "fake_action.heldout_auc.mean"
    )


def test_action_shuffled_is_report_only_diagnostic_not_endpoint_control():
    payload = runner.run_benchmark(small_config(seed=7))

    diagnostic = payload["controls"]["action_shuffled_diagnostic"]
    assert diagnostic["role"] == "report_only_diagnostic"
    assert diagnostic["status"] == "reported"
    assert "action_shuffled_diagnostic" in payload["hardgate"]["excluded_from_hardgate"]
    assert set(payload["hardgate"]["gates"]) == {
        "endpoint_heldout_auc",
        "fake_action_negative_control",
        "endpoint_fake_action_auc_gap",
    }
    assert "action_shuffled_diagnostic" in payload["metrics"]["arms"]


def test_fake_action_failure_fails_benchmark_without_using_shuffle_as_gate():
    payload = runner.run_benchmark(small_config(max_fake_action_auc=0.1))

    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["confound_resistant"] is False
    assert payload["hardgate"]["gates"]["fake_action_negative_control"]["status"] == "fail"
    assert payload["controls"]["action_shuffled_diagnostic"]["status"] == "reported"


def test_seed_results_are_paired_for_confidence_intervals():
    payload = runner.run_benchmark(small_config(seed_count=4))
    endpoint_auc = payload["metrics"]["arms"]["endpoint"]["heldout_auc"]
    fake_auc = payload["metrics"]["arms"]["fake_action"]["heldout_auc"]
    gap = payload["metrics"]["paired_differences"]["endpoint_minus_fake_action_auc"]

    assert endpoint_auc["n"] == 4
    assert fake_auc["n"] == 4
    assert gap["n"] == 4
    assert [row["seed"] for row in payload["metrics"]["seed_results"]] == [1717, 1718, 1719, 1720]
    assert gap["left_arm"] == "endpoint"
    assert gap["right_arm"] == "fake_action"


@pytest.mark.parametrize(
    ("overrides", "expected"),
    [
        ({"sample_count": 39}, "sample_count"),
        ({"seed_count": 1}, "seed_count"),
        ({"train_fraction": 0.05}, "train_fraction"),
        ({"observation_noise": -0.1}, "observation_noise"),
        ({"logistic_epochs": 0}, "logistic_epochs"),
        ({"learning_rate": 0.0}, "learning_rate"),
        ({"l2_penalty": -0.1}, "l2_penalty"),
        ({"min_endpoint_auc": 1.1}, "min_endpoint_auc"),
        ({"max_fake_action_auc": -0.1}, "max_fake_action_auc"),
        ({"min_endpoint_fake_auc_gap_ci_low": 1.1}, "min_endpoint_fake_auc_gap_ci_low"),
    ],
)
def test_config_validation_fails_closed(overrides, expected):
    with pytest.raises(ValueError, match=expected):
        runner.run_benchmark(small_config(**overrides))


def test_cli_writes_same_payload_shape_as_shared_api(tmp_path):
    output = tmp_path / "hpr.json"
    completed = subprocess.run(
        [
            sys.executable,
            "scripts/run_hpr_achievement.py",
            "--sample-count",
            "96",
            "--seed",
            "1717",
            "--seed-count",
            "5",
            "--observation-noise",
            "0.05",
            "--logistic-epochs",
            "120",
            "--output",
            str(output),
            "--stdout",
        ],
        check=True,
        text=True,
        capture_output=True,
    )

    written = json.loads(output.read_text(encoding="utf-8"))
    printed = json.loads(completed.stdout)
    api_payload = runner.run_benchmark(small_config())

    assert written == printed
    assert written == api_payload
