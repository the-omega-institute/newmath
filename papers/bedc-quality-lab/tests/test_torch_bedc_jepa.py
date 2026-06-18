import importlib.util

import numpy as np
import pytest

from bedc_quality_lab import torch_bedc_jepa
from bedc_quality_lab.bedc_jepa_world import make_boundary_gated_batch
from bedc_quality_lab.torch_bedc_jepa import (
    boundary_batch_action_array,
    run_torch_bedc_jepa_benchmark,
    run_torch_bedc_jepa_sweep,
    train_torch_bedc_jepa_surface,
)


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


def test_torch_bedc_jepa_surface_forwards_requested_device(monkeypatch):
    calls = []

    def fake_train(train, *, seed, epochs, weights, requested_device):
        calls.append(
            {
                "train": train,
                "seed": seed,
                "epochs": epochs,
                "weights": weights,
                "requested_device": requested_device,
            }
        )
        return {"device": requested_device}

    monkeypatch.setattr(torch_bedc_jepa, "_train_weighted_variant", fake_train)

    train = object()
    model = train_torch_bedc_jepa_surface(
        train,
        seed=17,
        bedc_objective=True,
        epochs=3,
        requested_device="cuda",
    )

    assert model == {"device": "cuda"}
    assert calls[0]["train"] is train
    assert calls[0]["seed"] == 17
    assert calls[0]["epochs"] == 3
    assert calls[0]["requested_device"] == "cuda"
    assert calls[0]["weights"]["gap_bce"] > 0.0


def test_boundary_gated_surface_exposes_action_conditioning():
    batch = make_boundary_gated_batch(16, rho=0.84, seed=9)
    action = boundary_batch_action_array(batch)

    assert action.shape == batch.z.shape
    assert action.dtype == batch.z.dtype
    assert np.allclose(batch.z_pair, 0.84 * batch.z + action)
