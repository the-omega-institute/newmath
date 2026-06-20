import json
import subprocess
import sys

import pytest

from scripts import run_hpr_achievement as runner


def small_config(**overrides):
    values = {
        "sample_count": 96,
        "seed": 1717,
        "train_fraction": 0.5,
        "observation_noise": 0.05,
        "min_endpoint_accuracy": 0.9,
        "max_fake_action_accuracy": 0.62,
    }
    values.update(overrides)
    return runner.HPRAchievementConfig(**values)


def test_run_benchmark_returns_json_compatible_contract():
    payload = runner.run_benchmark(small_config())
    reparsed = json.loads(json.dumps(payload, sort_keys=True))

    assert reparsed == payload
    assert payload["schema_id"] == runner.SCHEMA_ID
    assert payload["artifact_id"] == runner.ARTIFACT_ID
    assert payload["sample_summary"]["fake_action_source"] == "fresh_independent_rademacher"
    assert payload["hardgate"]["status"] == "pass"
    assert payload["metrics"]["endpoint_accuracy"] >= 0.9


def test_fake_action_is_independent_negative_control_and_hardgate_input():
    payload = runner.run_benchmark(small_config(seed=2001))

    assert payload["controls"]["fake_action"]["role"] == "negative_control"
    assert payload["controls"]["fake_action"]["source"] == "fresh_independent_rademacher"
    assert payload["controls"]["fake_action"]["status"] == "pass"
    assert payload["metrics"]["fake_action_control_accuracy"] <= payload["controls"]["fake_action"]["max_allowed"]
    assert payload["hardgate"]["gates"]["fake_action"]["metric"] == "fake_action_control_accuracy"


def test_action_shuffled_is_report_only_diagnostic_not_endpoint_control():
    payload = runner.run_benchmark(small_config(seed=7))

    diagnostic = payload["controls"]["action_shuffled_diagnostic"]
    assert diagnostic["role"] == "report_only_diagnostic"
    assert diagnostic["status"] == "reported"
    assert "action_shuffled_diagnostic" in payload["hardgate"]["excluded_from_hardgate"]
    assert set(payload["hardgate"]["gates"]) == {"endpoint", "fake_action"}
    assert "action_shuffled_diagnostic_accuracy" in payload["metrics"]


def test_fake_action_failure_fails_benchmark_without_using_shuffle_as_gate():
    payload = runner.run_benchmark(small_config(max_fake_action_accuracy=0.1))

    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["fake_action"]["status"] == "fail"
    assert payload["controls"]["action_shuffled_diagnostic"]["status"] == "reported"


@pytest.mark.parametrize(
    ("overrides", "expected"),
    [
        ({"sample_count": 19}, "sample_count"),
        ({"train_fraction": 0.05}, "train_fraction"),
        ({"observation_noise": -0.1}, "observation_noise"),
        ({"min_endpoint_accuracy": 1.1}, "min_endpoint_accuracy"),
        ({"max_fake_action_accuracy": -0.1}, "max_fake_action_accuracy"),
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
            "--observation-noise",
            "0.05",
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
