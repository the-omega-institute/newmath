from __future__ import annotations

import pytest


torch = pytest.importorskip("torch")

from bedc_quality_lab.cit_causal_transfer import CITConfig, run_arm, run_fresh_action, run_q_arm


pytestmark = pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA is unavailable")


def _cuda_config(**overrides):
    base = {
        "seed": 1726,
        "train_n": 192,
        "eval_n": 192,
        "hidden_dim": 12,
        "epochs": 80,
        "batch_size": 64,
        "bootstrap_samples": 80,
        "device": "cuda",
    }
    base.update(overrides)
    return CITConfig(**base)


def test_hard_independent_w_control_ci_covers_chance():
    result = run_fresh_action(_cuda_config(independent_w=True))
    ci = result["learned"]["ci"]

    assert ci["lower"] <= 0.5 <= ci["upper"]
    assert result["analytic_bayes"] == 0.5


def test_bayes_indifferent_learned_ci_covers_chance():
    result = run_arm(_cuda_config(bayes_indifferent=True, seed=1733))
    ci = result["learned"]["ci"]

    assert ci["lower"] <= 0.5 <= ci["upper"]
    assert result["analytic_bayes"] == 0.5


def test_learned_point_is_positive_and_bounded_by_bayes_tolerance():
    result = run_arm(_cuda_config(seed=1741))
    point = result["learned"]["point"]

    assert point > 0.5
    assert point <= result["analytic_bayes"] + 0.02


def test_q3_transfer_is_positive():
    result = run_q_arm(_cuda_config(q=3, seed=1759))

    assert result["config"]["q"] == 3
    assert result["learned"]["point"] > 0.5
