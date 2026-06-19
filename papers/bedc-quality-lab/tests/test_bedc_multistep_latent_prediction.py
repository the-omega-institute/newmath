from __future__ import annotations

import json

import numpy as np
import pytest

from bedc_quality_lab import bedc_multistep_latent_prediction as mlp
from bedc_quality_lab.bedc_multistep_latent_prediction import (
    LatentPredictionGateSpec,
    LatentRolloutBatch,
    PredictorSpec,
    run_multistep_latent_prediction_smoke,
)


def test_multistep_latent_prediction_packet_is_json_primitive_and_fail_closed():
    packet = run_multistep_latent_prediction_smoke(sample_count=16, horizon=3, seed=13)

    json.dumps(packet)
    assert packet["schema_id"] == "bedc-multistep-latent-prediction"
    assert packet["status"] == "executed"
    assert packet["record_scope"] == "local_smoke_contract"
    assert packet["evidence_chain"]["owner_module"] == (
        "bedc_quality_lab.bedc_multistep_latent_prediction"
    )
    assert packet["rollout_contract"]["sample_count"] == 16
    assert packet["rollout_contract"]["horizon"] == 3
    assert "rollout_batch" not in packet
    assert {row["family"] for row in packet["predictor_specs"]} == {
        "jepa_mlp",
        "gru",
        "rssm",
        "transformer",
    }
    assert {row["horizon"] for row in packet["runs"]} == {1, 3}
    assert any(row["action_conditioned"] for row in packet["runs"])
    assert all(row["planning_success"] is None for row in packet["runs"])
    assert packet["summary"]["run_count"] == len(packet["runs"])
    assert packet["summary"]["family_count"] == 4
    assert packet["summary"]["planning_success_claimed"] is False
    assert "predictor_spec" not in packet
    assert packet["hardgate"]["status"] in {"pass", "source_debt"}
    assert "gate_spec" not in packet
    assert "rollout_contract" in packet["hardgate"]["required_record_fields"]
    assert "predictor_specs" in packet["hardgate"]["required_record_fields"]
    assert "runs" in packet["hardgate"]["required_record_fields"]
    assert packet["metrics"]["rollout_mse"] >= 0.0
    assert 0.0 <= packet["metrics"]["latent_prediction_score"] <= 1.0
    assert 0.0 <= packet["metrics"]["gap_detection_auc"] <= 1.0
    assert 0.0 <= packet["metrics"]["certified_coverage"] <= 1.0
    assert 0.0 <= packet["metrics"]["unlogged_error_rate"] <= 1.0
    assert packet["claim_scope"]["minigrid_planning_success"] == "not_claimed"
    assert packet["claim_scope"]["full_4090_sweep"] == "not_claimed"
    assert "MiniGrid planning success" in packet["cannot_claim"]
    assert "quality backend full-sweep admission" in packet["cannot_claim"]


def test_multistep_latent_prediction_schema_owner_types_are_local():
    assert LatentRolloutBatch.__module__ == "bedc_quality_lab.bedc_multistep_latent_prediction"
    assert PredictorSpec.__module__ == "bedc_quality_lab.bedc_multistep_latent_prediction"
    assert LatentPredictionGateSpec.__module__ == (
        "bedc_quality_lab.bedc_multistep_latent_prediction"
    )


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"sample_count": 0}, "sample_count"),
        ({"horizon": 0}, "horizon"),
    ],
)
def test_latent_rollout_batch_rejects_nonpositive_shape_controls(kwargs, message):
    with pytest.raises(ValueError, match=message):
        mlp.make_latent_rollout_batch(**kwargs)


def test_latent_rollout_batch_supports_nondefault_latent_and_action_shapes():
    batch = mlp.make_latent_rollout_batch(
        sample_count=7,
        horizon=5,
        latent_dim=4,
        action_dim=3,
        seed=23,
        split="alternate",
    )

    assert batch.initial_latents.shape == (7, 4)
    assert batch.actions.shape == (7, 5, 3)
    assert batch.target_latents.shape == (7, 5, 4)
    assert batch.unsafe_transition.shape == (7, 5)
    assert batch.unsafe_transition.dtype == np.bool_
    assert np.isfinite(batch.target_latents).all()
    assert batch.to_record() == {
        "environment_id": "boundary-gated-ou-latent-rollout",
        "split": "alternate",
        "horizon": 5,
        "sample_count": 7,
        "latent_dim": 4,
        "action_dim": 3,
        "unsafe_transition_rate": float(np.mean(batch.unsafe_transition)),
    }


def _latent_prediction_gate() -> LatentPredictionGateSpec:
    return LatentPredictionGateSpec(
        gate_id="test-gate",
        min_gap_detection_auc=0.70,
        min_certified_coverage=0.80,
        max_unlogged_error_rate=0.05,
        min_coverage=0.80,
        required_record_fields=("rollout_contract", "predictor_specs", "runs"),
    )


def _gate_run(
    *,
    gap_detection_auc: float = 0.75,
    certified_coverage: float = 0.85,
    unlogged_error_rate: float = 0.03,
) -> dict[str, float]:
    return {
        "gap_detection_auc": gap_detection_auc,
        "certified_coverage": certified_coverage,
        "unlogged_error_rate": unlogged_error_rate,
    }


def test_latent_prediction_gate_rejects_empty_runs():
    result = _latent_prediction_gate().evaluate([])

    assert result["status"] == "source_debt"
    assert result["failure_reasons"] == ["no predictor runs recorded"]
    assert result["required_record_fields"] == ["rollout_contract", "predictor_specs", "runs"]


@pytest.mark.parametrize(
    "run",
    [
        _gate_run(gap_detection_auc=0.69),
        _gate_run(certified_coverage=0.79),
        _gate_run(unlogged_error_rate=0.06),
    ],
)
def test_latent_prediction_gate_rejects_threshold_failures(run):
    result = _latent_prediction_gate().evaluate([run])

    assert result["status"] == "source_debt"


def test_latent_prediction_gate_accepts_rows_that_meet_thresholds():
    result = _latent_prediction_gate().evaluate(
        [
            _gate_run(gap_detection_auc=0.74, certified_coverage=0.88, unlogged_error_rate=0.02),
            _gate_run(gap_detection_auc=0.72, certified_coverage=0.84, unlogged_error_rate=0.04),
        ]
    )

    assert result["status"] == "pass"
    assert result["observed"] == {
        "min_gap_detection_auc": 0.72,
        "min_certified_coverage": 0.84,
        "max_unlogged_error_rate": 0.04,
    }


def _passing_gpu_evidence() -> dict[str, object]:
    return {
        "schema_id": "bedc-gpu-evidence",
        "torch": {
            "cuda_available": True,
            "cuda_device_name": "Test CUDA",
            "device_resolution": {
                "requested_device": "cuda",
                "resolved_device": "cuda",
                "resolution_status": "available",
            },
        },
        "nvidia_smi": {
            "available": True,
            "gpus": [{"name": "Test CUDA", "driver_version": "555.12", "memory_total": "8192 MiB"}],
        },
    }


def _failing_gpu_evidence() -> dict[str, object]:
    evidence = _passing_gpu_evidence()
    evidence["torch"]["cuda_available"] = False
    evidence["torch"]["device_resolution"]["resolved_device"] = ""
    evidence["nvidia_smi"]["available"] = False
    evidence["nvidia_smi"]["gpus"] = []
    return evidence


def _install_fake_surface(monkeypatch) -> None:
    def train_surface(train, *, seed, bedc_objective, epochs, requested_device):
        return {
            "seed": seed,
            "bedc_objective": bedc_objective,
            "device": requested_device,
            "train_rows": train.x.shape[0],
            "epochs": epochs,
        }

    def score_surface(model, batch):
        rows = batch.x.shape[0]
        return {
            "latent": np.zeros((rows, 2), dtype=np.float64),
            "distinction": np.full(rows, 0.75 if model["bedc_objective"] else 0.25, dtype=np.float64),
            "gap": np.full(rows, 0.75 if model["bedc_objective"] else 0.25, dtype=np.float64),
        }

    def evaluate_surface(name, scores, batch):
        bedc = name == "bedc_objective"
        return {
            "linear_identifiability_r2": 0.92 if bedc else 0.86,
            "gap_detection_auc": 0.91 if bedc else 0.70,
            "certified_coverage": 0.83 if bedc else 0.70,
            "unlogged_error_rate": 0.01 if bedc else 0.08,
        }

    def rollout(model, batch, *, steps):
        rows = batch.x.shape[0]
        value = 0.0 if model["bedc_objective"] else 1.0
        return np.full((rows, 2), value, dtype=np.float64)

    monkeypatch.setattr(mlp, "train_torch_bedc_jepa_surface", train_surface)
    monkeypatch.setattr(mlp, "score_torch_bedc_jepa_surface", score_surface)
    monkeypatch.setattr(mlp, "evaluate_torch_bedc_jepa_surface", evaluate_surface)
    monkeypatch.setattr(mlp, "_rollout_latents", rollout)
    monkeypatch.setattr(mlp, "_rollout_target", lambda batch, *, steps: np.zeros((batch.x.shape[0], 2), dtype=np.float64))


def test_multistep_report_uses_paired_seeds_gpu_evidence_and_gap_hardgates(monkeypatch):
    _install_fake_surface(monkeypatch)

    report = mlp.run_bedc_multistep_latent_prediction(
        seeds=(1, 2, 3, 4, 5),
        train_count=12,
        test_count=8,
        epochs=2,
        steps=3,
        device="cuda",
        gpu_evidence=_passing_gpu_evidence(),
    )

    assert report["schema_id"] == "bedc-multistep-latent-prediction"
    assert report["source"]["training"] == "torch-bedc-jepa-shared-surface"
    assert report["seed_count"] == 5
    assert report["hardgates"]["status"] == "passed"
    assert report["hardgates"]["claim_allowed"] is True
    assert report["hardgates"]["gates"] == {
        "gpu_evidence": True,
        "seed_count": True,
        "paired_bootstrap_ci": True,
        "gap_preservation": True,
    }
    assert report["paired_deltas"]["rollout_mse_reduction"] == [1.0, 1.0, 1.0, 1.0, 1.0]
    assert "gap_detection_auc" in report["same_split_metrics"]
    assert len(report["runs"]) == 5


def test_multistep_report_blocks_claim_when_device_is_not_cuda(monkeypatch):
    _install_fake_surface(monkeypatch)

    report = mlp.run_bedc_multistep_latent_prediction(
        seeds=(1, 2, 3, 4, 5),
        train_count=8,
        test_count=6,
        epochs=1,
        steps=2,
        device="cpu",
        gpu_evidence=_passing_gpu_evidence(),
    )

    assert report["hardgates"]["status"] == "failed"
    assert report["hardgates"]["gates"]["gpu_evidence"] is False
    assert report["cannot_claim"]


def test_multistep_report_blocks_claim_when_seed_count_is_too_small(monkeypatch):
    _install_fake_surface(monkeypatch)

    report = mlp.run_bedc_multistep_latent_prediction(
        seeds=(1, 2, 3, 4),
        train_count=8,
        test_count=6,
        epochs=1,
        steps=2,
        device="cuda",
        gpu_evidence=_passing_gpu_evidence(),
    )

    assert report["seed_count"] == 4
    assert report["hardgates"]["status"] == "failed"
    assert report["hardgates"]["gates"]["seed_count"] is False
    assert report["hardgates"]["gates"]["paired_bootstrap_ci"] is False
    assert "seed_count" in report["hardgates"]["claim_block_reason"]


def test_multistep_report_does_not_train_when_cuda_evidence_is_missing(monkeypatch):
    def train_surface(*args, **kwargs):
        raise AssertionError("training must not run without CUDA evidence")

    monkeypatch.setattr(mlp, "train_torch_bedc_jepa_surface", train_surface)

    report = mlp.run_bedc_multistep_latent_prediction(
        seeds=(1, 2, 3, 4, 5),
        train_count=8,
        test_count=6,
        epochs=1,
        steps=2,
        device="cuda",
        gpu_evidence=_failing_gpu_evidence(),
    )

    assert report["status"] == "unavailable"
    assert report["runs"] == []
    assert report["hardgates"]["gates"]["gpu_evidence"] is False
    assert report["hardgates"]["claim_allowed"] is False


def test_multistep_report_requires_nonempty_seed_set():
    with pytest.raises(ValueError, match="seeds"):
        mlp.run_bedc_multistep_latent_prediction(seeds=(), gpu_evidence=_passing_gpu_evidence())


@pytest.mark.parametrize(
    ("kwargs", "message"),
    [
        ({"train_count": 0}, "train_count and test_count"),
        ({"test_count": 0}, "train_count and test_count"),
        ({"steps": 0}, "steps"),
    ],
)
def test_multistep_report_rejects_nonpositive_counts_and_steps(kwargs, message):
    with pytest.raises(ValueError, match=message):
        mlp.run_bedc_multistep_latent_prediction(
            seeds=(1,),
            gpu_evidence=_passing_gpu_evidence(),
            **kwargs,
        )
