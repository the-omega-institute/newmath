from __future__ import annotations

import numpy as np
import pytest

from bedc_quality_lab import bedc_multistep_latent_prediction as mlp


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
