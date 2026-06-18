"""K-step action-conditioned latent prediction on the BEDC-JEPA torch surface."""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import certified_coverage, gap_detection_auc, unlogged_error_rate
from bedc_quality_lab.bedc_jepa_world import BoundaryGatedBatch, make_boundary_gated_batch
from bedc_quality_lab.gpu_evidence import collect_gpu_evidence, gpu_evidence_passes
from bedc_quality_lab.metrics import linear_identifiability_r2
from bedc_quality_lab.model import require_torch
from bedc_quality_lab.torch_bedc_jepa import (
    boundary_batch_action_array,
    evaluate_torch_bedc_jepa_surface,
    score_torch_bedc_jepa_surface,
    train_torch_bedc_jepa_surface,
)


DEFAULT_SEEDS = (4242, 4259, 4276, 4293, 4310)


def _ci95(values: Sequence[float]) -> float:
    if len(values) <= 1:
        return 0.0
    array = np.asarray(values, dtype=np.float64)
    return float(1.96 * np.std(array, ddof=1) / np.sqrt(array.shape[0]))


def _bootstrap_ci(
    values: Sequence[float],
    *,
    seed: int = 20260618,
    samples: int = 1000,
) -> dict[str, float]:
    array = np.asarray(values, dtype=np.float64)
    if array.size == 0:
        return {"mean": 0.0, "low": 0.0, "high": 0.0}
    if array.size == 1:
        value = float(array[0])
        return {"mean": value, "low": value, "high": value}
    rng = np.random.default_rng(seed)
    draws = rng.choice(array, size=(int(samples), array.size), replace=True)
    means = np.mean(draws, axis=1)
    return {
        "mean": float(np.mean(array)),
        "low": float(np.percentile(means, 2.5)),
        "high": float(np.percentile(means, 97.5)),
    }


def _rollout_latents(model: dict[str, Any], batch: BoundaryGatedBatch, *, steps: int) -> np.ndarray:
    if steps < 1:
        raise ValueError("steps must be positive")
    torch = require_torch()
    device = str(model["device"])
    x = torch.as_tensor(batch.x, dtype=torch.float32, device=device)
    action = torch.as_tensor(boundary_batch_action_array(batch), dtype=torch.float32, device=device)
    with torch.no_grad():
        z = model["encoder"](x)
        for _ in range(int(steps)):
            z = model["predictor"](torch.cat([z, action], dim=1))
    return z.detach().cpu().numpy()


def _rollout_target(batch: BoundaryGatedBatch, *, steps: int) -> np.ndarray:
    if steps < 1:
        raise ValueError("steps must be positive")
    current = np.asarray(batch.z, dtype=np.float64)
    action = boundary_batch_action_array(batch)
    for _ in range(int(steps)):
        current = 0.84 * current + action
    return current


def _paired_split(seed: int, train_count: int, test_count: int) -> tuple[BoundaryGatedBatch, BoundaryGatedBatch]:
    train = make_boundary_gated_batch(train_count, rho=0.84, radius=1.0, gap_width=0.14, seed=int(seed))
    test = make_boundary_gated_batch(test_count, rho=0.84, radius=1.0, gap_width=0.14, seed=int(seed) + 1)
    return train, test


def _system_row(
    *,
    name: str,
    model: dict[str, Any],
    test: BoundaryGatedBatch,
    steps: int,
) -> dict[str, float | str]:
    scores = score_torch_bedc_jepa_surface(model, test)
    eval_metrics = evaluate_torch_bedc_jepa_surface(name, scores, test)
    rolled = _rollout_latents(model, test, steps=steps)
    target = _rollout_target(test, steps=steps)
    rollout_mse = float(np.mean((np.asarray(rolled, dtype=np.float64) - target) ** 2))
    rollout_r2 = linear_identifiability_r2(rolled, target)
    return {
        "system_name": name,
        "latent_r2": float(eval_metrics["linear_identifiability_r2"]),
        "rollout_r2": rollout_r2,
        "rollout_mse": rollout_mse,
        "gap_detection_auc": float(eval_metrics["gap_detection_auc"]),
        "certified_coverage": float(eval_metrics["certified_coverage"]),
        "unlogged_error_rate": float(eval_metrics["unlogged_error_rate"]),
    }


def _summarize(rows: Sequence[dict[str, float | str]]) -> dict[str, float]:
    keys = (
        "latent_r2",
        "rollout_r2",
        "rollout_mse",
        "gap_detection_auc",
        "certified_coverage",
        "unlogged_error_rate",
    )
    return {
        f"{key}_mean": float(np.mean([float(row[key]) for row in rows]))
        for key in keys
    } | {
        f"{key}_ci95": _ci95([float(row[key]) for row in rows])
        for key in keys
    }


def _hardgates(
    *,
    seeds: Sequence[int],
    gpu_evidence: dict[str, Any],
    device: str,
    deltas: dict[str, Sequence[float]],
    gap_preservation_tolerance: float,
) -> dict[str, Any]:
    rollout_improvement_ci = _bootstrap_ci(deltas["rollout_mse_reduction"])
    latent_r2_delta_ci = _bootstrap_ci(deltas["latent_r2_delta"])
    gap_auc_delta_ci = _bootstrap_ci(deltas["gap_auc_delta"])
    coverage_delta_ci = _bootstrap_ci(deltas["coverage_delta"])
    unlogged_delta_ci = _bootstrap_ci(deltas["unlogged_error_reduction"])
    gate_rows = {
        "gpu_evidence": device == "cuda" and gpu_evidence_passes(gpu_evidence),
        "seed_count": len(seeds) >= 5,
        "paired_bootstrap_ci": len(deltas["rollout_mse_reduction"]) >= 5 and rollout_improvement_ci["low"] > 0.0,
        "gap_preservation": (
            len(deltas["gap_auc_delta"]) >= 5
            and gap_auc_delta_ci["low"] >= -gap_preservation_tolerance
            and coverage_delta_ci["low"] >= -gap_preservation_tolerance
            and unlogged_delta_ci["low"] >= -gap_preservation_tolerance
        ),
    }
    return {
        "status": "passed" if all(gate_rows.values()) else "failed",
        "gates": gate_rows,
        "paired_bootstrap_ci": {
            "rollout_mse_reduction": rollout_improvement_ci,
            "latent_r2_delta": latent_r2_delta_ci,
            "gap_auc_delta": gap_auc_delta_ci,
            "coverage_delta": coverage_delta_ci,
            "unlogged_error_reduction": unlogged_delta_ci,
        },
        "claim_allowed": bool(all(gate_rows.values())),
        "claim_block_reason": []
        if all(gate_rows.values())
        else [name for name, passed in gate_rows.items() if not passed],
    }


def run_bedc_multistep_latent_prediction(
    *,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    train_count: int = 1536,
    test_count: int = 768,
    epochs: int = 220,
    steps: int = 3,
    device: str = "cuda",
    gpu_evidence: dict[str, Any] | None = None,
    gap_preservation_tolerance: float = 0.02,
) -> dict[str, Any]:
    if len(seeds) == 0:
        raise ValueError("seeds must not be empty")
    if train_count < 1 or test_count < 1:
        raise ValueError("train_count and test_count must be positive")
    if steps < 1:
        raise ValueError("steps must be positive")

    evidence = gpu_evidence if gpu_evidence is not None else collect_gpu_evidence(requested_device=device)
    empty_deltas: dict[str, list[float]] = {
        "rollout_mse_reduction": [],
        "latent_r2_delta": [],
        "gap_auc_delta": [],
        "coverage_delta": [],
        "unlogged_error_reduction": [],
    }
    if device == "cuda" and not gpu_evidence_passes(evidence):
        hardgates = _hardgates(
            seeds=[int(seed) for seed in seeds],
            gpu_evidence=evidence,
            device=device,
            deltas=empty_deltas,
            gap_preservation_tolerance=float(gap_preservation_tolerance),
        )
        return {
            "schema_id": "bedc-multistep-latent-prediction",
            "status": "unavailable",
            "source": {
                "name": "boundary-gated-ou-world",
                "training": "torch-bedc-jepa-shared-surface",
                "train_count": int(train_count),
                "test_count": int(test_count),
                "epochs": int(epochs),
                "steps": int(steps),
                "device": device,
            },
            "seeds": [int(seed) for seed in seeds],
            "seed_count": int(len(seeds)),
            "gpu_evidence": evidence,
            "systems": {},
            "runs": [],
            "paired_deltas": empty_deltas,
            "hardgates": hardgates,
            "same_split_metrics": [
                "latent_r2",
                "rollout_mse",
                "gap_detection_auc",
                "certified_coverage",
                "unlogged_error_rate",
            ],
            "cannot_claim": [
                "multistep latent-prediction capability improvement without CUDA GPU evidence"
            ],
        }
    run_rows: list[dict[str, Any]] = []
    by_system: dict[str, list[dict[str, float | str]]] = {"latent_only": [], "bedc_objective": []}
    deltas: dict[str, list[float]] = {
        "rollout_mse_reduction": [],
        "latent_r2_delta": [],
        "gap_auc_delta": [],
        "coverage_delta": [],
        "unlogged_error_reduction": [],
    }
    for seed in seeds:
        train, test = _paired_split(int(seed), int(train_count), int(test_count))
        latent_model = train_torch_bedc_jepa_surface(
            train,
            seed=int(seed),
            bedc_objective=False,
            epochs=int(epochs),
            requested_device=device,
        )
        bedc_model = train_torch_bedc_jepa_surface(
            train,
            seed=int(seed),
            bedc_objective=True,
            epochs=int(epochs),
            requested_device=device,
        )
        latent_row = _system_row(name="latent_only", model=latent_model, test=test, steps=int(steps))
        bedc_row = _system_row(name="bedc_objective", model=bedc_model, test=test, steps=int(steps))
        by_system["latent_only"].append(latent_row)
        by_system["bedc_objective"].append(bedc_row)
        deltas["rollout_mse_reduction"].append(float(latent_row["rollout_mse"]) - float(bedc_row["rollout_mse"]))
        deltas["latent_r2_delta"].append(float(bedc_row["latent_r2"]) - float(latent_row["latent_r2"]))
        deltas["gap_auc_delta"].append(float(bedc_row["gap_detection_auc"]) - float(latent_row["gap_detection_auc"]))
        deltas["coverage_delta"].append(float(bedc_row["certified_coverage"]) - float(latent_row["certified_coverage"]))
        deltas["unlogged_error_reduction"].append(
            float(latent_row["unlogged_error_rate"]) - float(bedc_row["unlogged_error_rate"])
        )
        run_rows.append(
            {
                "seed": float(seed),
                "split": "same boundary-gated OU train/test split for latent, rollout, gap, coverage, and unlogged-error metrics",
                "systems": {
                    "latent_only": latent_row,
                    "bedc_objective": bedc_row,
                },
                "deltas": {key: float(values[-1]) for key, values in deltas.items()},
            }
        )
    hardgates = _hardgates(
        seeds=[int(seed) for seed in seeds],
        gpu_evidence=evidence,
        device=device,
        deltas=deltas,
        gap_preservation_tolerance=float(gap_preservation_tolerance),
    )
    return {
        "schema_id": "bedc-multistep-latent-prediction",
        "status": "executed",
        "source": {
            "name": "boundary-gated-ou-world",
            "training": "torch-bedc-jepa-shared-surface",
            "train_count": int(train_count),
            "test_count": int(test_count),
            "epochs": int(epochs),
            "steps": int(steps),
            "device": device,
        },
        "seeds": [int(seed) for seed in seeds],
        "seed_count": int(len(seeds)),
        "gpu_evidence": evidence,
        "systems": {
            "latent_only": _summarize(by_system["latent_only"]),
            "bedc_objective": _summarize(by_system["bedc_objective"]),
        },
        "runs": run_rows,
        "paired_deltas": {key: [float(value) for value in values] for key, values in deltas.items()},
        "hardgates": hardgates,
        "same_split_metrics": [
            "latent_r2",
            "rollout_mse",
            "gap_detection_auc",
            "certified_coverage",
            "unlogged_error_rate",
        ],
        "cannot_claim": []
        if hardgates["claim_allowed"]
        else [
            "multistep latent-prediction capability improvement without passing GPU evidence, paired seeds, bootstrap CI, and gap-preservation gates"
        ],
    }


def summarize_gap_metrics(batch: BoundaryGatedBatch, scores: dict[str, np.ndarray]) -> dict[str, float]:
    return {
        "gap_detection_auc": gap_detection_auc(scores["gap"], batch.gap),
        "certified_coverage": certified_coverage(scores["gap"]),
        "unlogged_error_rate": unlogged_error_rate(scores["distinction"], batch.distinction, scores["gap"]),
    }
