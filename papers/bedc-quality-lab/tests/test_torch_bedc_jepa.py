import importlib.util

import pytest

from bedc_quality_lab.torch_bedc_jepa import run_torch_bedc_jepa_benchmark, run_torch_bedc_jepa_sweep


def test_torch_bedc_jepa_objective_trains_gap_and_distinction_heads():
    if importlib.util.find_spec("torch") is None:
        pytest.skip("torch is not installed")

    summary = run_torch_bedc_jepa_benchmark(seed=4242)

    assert summary["source"]["training"] == "torch-gradient"
    assert "unlogged_error_penalty" in summary["objective_terms"]

    latent = summary["systems"]["latent_only"]
    bedc = summary["systems"]["bedc_objective"]
    deltas = summary["deltas"]

    assert latent["system_name"] == "torch-latent-only"
    assert bedc["system_name"] == "torch-bedc-jepa-objective"
    assert bedc["gap_detection_auc"] > latent["gap_detection_auc"]
    assert bedc["unlogged_error_rate"] <= latent["unlogged_error_rate"]
    assert bedc["unlogged_error_rate"] == 0.0
    assert bedc["bedc_debt_score"] < latent["bedc_debt_score"]
    assert deltas["gap_auc_gain"] > 0.20
    assert deltas["unlogged_error_reduction"] >= 0.0
    assert deltas["debt_reduction"] > 0.05
    assert abs(deltas["latent_r2_delta"]) < 1e-8


def test_torch_bedc_jepa_sweep_aggregates_gradient_objective_gains():
    if importlib.util.find_spec("torch") is None:
        pytest.skip("torch is not installed")

    sweep = run_torch_bedc_jepa_sweep(seeds=(4242, 4259, 4276))

    assert sweep["seed_count"] == 3.0
    assert sweep["seeds"] == [4242.0, 4259.0, 4276.0]
    assert sweep["gap_auc_gain_mean"] > 0.20
    assert sweep["debt_reduction_mean"] > 0.05
    assert sweep["unlogged_error_reduction_mean"] >= 0.0
    assert sweep["latent_r2_delta_abs_max"] < 1e-8
    assert sweep["gap_auc_win_rate"] >= 0.75
    assert sweep["debt_win_rate"] >= 0.75
    assert sweep["unlogged_error_win_rate"] >= 0.75
    assert len(sweep["runs"]) == 3
