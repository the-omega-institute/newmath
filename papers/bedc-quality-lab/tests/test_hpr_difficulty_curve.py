import json
import math
import subprocess
import sys

import pytest

from scripts import run_hpr_control_verify as controls
from scripts import run_hpr_difficulty_curve as runner
from scripts import run_hpr_empirical_bayes_curve as empirical


def small_config(**overrides):
    values = {
        "sample_count": 512,
        "seed": 1724,
        "sigma": 1.0,
        "complexity_values": (0.2, 0.6),
        "horizon_values": (1, 4),
        "learned_empirical_max_gap": 0.03,
        "empirical_analytic_max_gap": 0.08,
    }
    values.update(overrides)
    return runner.HPRDifficultyConfig(**values)


def test_matched_pair_bayes_reference_has_no_independent_draw_sqrt_two_factor():
    complexity = 0.4
    horizon = 9
    sigma = 1.25

    observed = runner.matched_pair_bayes_accuracy(complexity, horizon, sigma)
    expected = 0.5 * (1.0 + math.erf((complexity * math.sqrt(horizon) / sigma) / math.sqrt(2.0)))
    independent_draw = 0.5 * (
        1.0 + math.erf((math.sqrt(2.0) * complexity * math.sqrt(horizon) / sigma) / math.sqrt(2.0))
    )

    assert observed == pytest.approx(expected)
    assert observed != pytest.approx(independent_draw)


def test_difficulty_curve_separates_closed_form_reference_from_learned_metrics():
    payload = runner.run_curve(small_config())
    reparsed = json.loads(json.dumps(payload, sort_keys=True))

    assert reparsed == payload
    assert payload["schema_id"] == runner.SCHEMA_ID
    assert payload["analytic_reference_contract"]["formula"] == "Phi(C * sqrt(T) / sigma)"
    assert payload["analytic_reference_contract"]["metric_role"] == "closed_form_reference"
    assert payload["hardgate"]["status"] == "pass"

    for row in payload["difficulty_curve"]:
        assert row["analytic_reference"]["reference_id"] == runner.ANALYTIC_REFERENCE_ID
        assert row["learned_metrics"]["metric_role"] == "learned_model_metric"
        assert row["analytic_reference"]["accuracy"] != row["learned_metrics"]["heldout_accuracy"]["mean"]


def test_learned_empirical_proximity_is_bounded():
    payload = runner.run_curve(small_config(seed=2001))
    gate = payload["hardgate"]["gates"]["learned_empirical_proximity"]

    assert gate["status"] == "pass"
    assert gate["max_gap"] <= gate["max_allowed"]


def test_empirical_analytic_proximity_failure_fails_aggregate_hardgate():
    payload = runner.run_curve(small_config(empirical_analytic_max_gap=0.0))
    gate = payload["hardgate"]["gates"]["empirical_analytic_proximity"]

    assert gate["status"] == "fail"
    assert gate["max_gap"] > gate["max_allowed"]
    assert payload["hardgate"]["status"] == "fail"


def test_obs_only_and_independent_fresh_action_controls_include_chance():
    payload = runner.run_curve(small_config())

    obs_only = payload["controls"]["obs_only"]["accuracy"]
    fresh_action = payload["controls"]["independent_fresh_action"]["accuracy"]
    assert obs_only["ci95_low"] <= 0.5 <= obs_only["ci95_high"]
    assert fresh_action["ci95_low"] <= 0.5 <= fresh_action["ci95_high"]
    assert payload["controls"]["independent_fresh_action"]["source"] == "fresh_independent_rademacher"
    assert payload["hardgate"]["gates"]["obs_only_chance_control"]["status"] == "pass"
    assert payload["hardgate"]["gates"]["independent_fresh_action_chance_control"]["status"] == "pass"


def test_empirical_bayes_curve_exposes_only_reference_rows():
    payload = empirical.run_empirical_bayes_curve(small_config())

    assert payload["schema_id"] == empirical.SCHEMA_ID
    assert payload["source_schema_id"] == runner.SCHEMA_ID
    assert payload["hardgate"]["status"] == "pass"
    assert set(payload["curve"][0]) == {
        "complexity",
        "horizon",
        "analytic_reference",
        "empirical_reference",
    }


def test_control_verify_reports_only_control_gates():
    payload = controls.run_control_verify(small_config())

    assert payload["schema_id"] == controls.SCHEMA_ID
    assert payload["hardgate"]["status"] == "pass"
    assert set(payload["hardgate"]["gates"]) == {
        "obs_only_chance_control",
        "independent_fresh_action_chance_control",
    }


@pytest.mark.parametrize(
    ("overrides", "expected"),
    [
        ({"sample_count": 39}, "sample_count"),
        ({"sigma": 0.0}, "sigma"),
        ({"complexity_values": ()}, "complexity_values"),
        ({"complexity_values": (-0.1,)}, "complexity_values"),
        ({"horizon_values": ()}, "horizon_values"),
        ({"horizon_values": (0,)}, "horizon_values"),
        ({"learned_empirical_max_gap": -0.1}, "learned_empirical_max_gap"),
        ({"empirical_analytic_max_gap": -0.1}, "empirical_analytic_max_gap"),
    ],
)
def test_config_validation_fails_closed(overrides, expected):
    with pytest.raises(ValueError, match=expected):
        runner.run_curve(small_config(**overrides))


def run_cli(script: str, output, *extra_args: str):
    return subprocess.run(
        [
            sys.executable,
            script,
            "--sample-count",
            "512",
            "--seed",
            "1724",
            "--sigma",
            "1.0",
            "--complexity-values",
            "0.2,0.6",
            "--horizon-values",
            "1,4",
            "--empirical-analytic-max-gap",
            "0.08",
            "--output",
            str(output),
            "--stdout",
            *extra_args,
        ],
        text=True,
        capture_output=True,
    )


def test_cli_writes_same_payload_shape_as_shared_api(tmp_path):
    output = tmp_path / "hpr-difficulty.json"
    completed = run_cli("scripts/run_hpr_difficulty_curve.py", output)

    assert completed.returncode == 0
    written = json.loads(output.read_text(encoding="utf-8"))
    printed = json.loads(completed.stdout)
    api_payload = runner.run_curve(small_config())

    assert written == printed
    assert written == api_payload


def test_cli_returns_nonzero_when_proximity_gate_fails(tmp_path):
    output = tmp_path / "hpr-difficulty-fail.json"
    completed = run_cli("scripts/run_hpr_difficulty_curve.py", output, "--empirical-analytic-max-gap", "0.0")

    assert completed.returncode == 1
    written = json.loads(output.read_text(encoding="utf-8"))
    printed = json.loads(completed.stdout)
    assert written == printed
    assert written["hardgate"]["status"] == "fail"
    assert written["hardgate"]["gates"]["empirical_analytic_proximity"]["status"] == "fail"


def test_empirical_bayes_cli_writes_reference_projection(tmp_path):
    output = tmp_path / "hpr-empirical-bayes.json"
    completed = run_cli("scripts/run_hpr_empirical_bayes_curve.py", output)

    assert completed.returncode == 0
    written = json.loads(output.read_text(encoding="utf-8"))
    printed = json.loads(completed.stdout)
    api_payload = empirical.run_empirical_bayes_curve(small_config())

    assert written == printed
    assert written == api_payload
    assert written["schema_id"] == empirical.SCHEMA_ID
    assert set(written["curve"][0]) == {
        "complexity",
        "horizon",
        "analytic_reference",
        "empirical_reference",
    }


def test_control_verify_cli_writes_control_projection(tmp_path):
    output = tmp_path / "hpr-control-verify.json"
    completed = run_cli("scripts/run_hpr_control_verify.py", output)

    assert completed.returncode == 0
    written = json.loads(output.read_text(encoding="utf-8"))
    printed = json.loads(completed.stdout)
    api_payload = controls.run_control_verify(small_config())

    assert written == printed
    assert written == api_payload
    assert written["schema_id"] == controls.SCHEMA_ID
    assert set(written["hardgate"]["gates"]) == {
        "obs_only_chance_control",
        "independent_fresh_action_chance_control",
    }
