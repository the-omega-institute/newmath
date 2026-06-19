"""K-step action-conditioned latent prediction evidence for BEDC-JEPA."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import asdict, dataclass
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


@dataclass(frozen=True)
class LatentRolloutBatch:
    environment_id: str
    split: str
    horizon: int
    initial_latents: np.ndarray
    actions: np.ndarray
    target_latents: np.ndarray
    unsafe_transition: np.ndarray

    def to_record(self) -> dict[str, Any]:
        return {
            "environment_id": self.environment_id,
            "split": self.split,
            "horizon": int(self.horizon),
            "sample_count": int(self.initial_latents.shape[0]),
            "latent_dim": int(self.initial_latents.shape[1]),
            "action_dim": int(self.actions.shape[2]),
            "unsafe_transition_rate": float(np.mean(self.unsafe_transition)),
        }


@dataclass(frozen=True)
class PredictorSpec:
    predictor_id: str
    family: str
    latent_dim: int
    action_dim: int
    horizon: int
    lambda_gap: float
    lambda_latent: float
    action_conditioned: bool
    training_status: str
    fit_method: str

    def to_record(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class LatentPredictionGateSpec:
    gate_id: str
    min_gap_detection_auc: float
    min_certified_coverage: float
    max_unlogged_error_rate: float
    min_coverage: float
    required_record_fields: tuple[str, ...]

    def evaluate(self, runs: list[dict[str, Any]]) -> dict[str, Any]:
        if not runs:
            return {
                "gate_id": self.gate_id,
                "status": "source_debt",
                "thresholds": self.thresholds(),
                "required_record_fields": list(self.required_record_fields),
                "failure_reasons": ["no predictor runs recorded"],
            }
        gap_auc = min(float(run["gap_detection_auc"]) for run in runs)
        coverage = min(float(run["certified_coverage"]) for run in runs)
        unlogged = max(float(run["unlogged_error_rate"]) for run in runs)
        passes = (
            gap_auc >= self.min_gap_detection_auc
            and coverage >= self.min_certified_coverage
            and unlogged <= self.max_unlogged_error_rate
        )
        return {
            "gate_id": self.gate_id,
            "status": "pass" if passes else "source_debt",
            "thresholds": self.thresholds(),
            "observed": {
                "min_gap_detection_auc": gap_auc,
                "min_certified_coverage": coverage,
                "max_unlogged_error_rate": unlogged,
            },
            "required_record_fields": list(self.required_record_fields),
        }

    def thresholds(self) -> dict[str, float]:
        return {
            "min_gap_detection_auc": float(self.min_gap_detection_auc),
            "min_certified_coverage": float(self.min_certified_coverage),
            "max_unlogged_error_rate": float(self.max_unlogged_error_rate),
            "min_coverage": float(self.min_coverage),
        }


def make_latent_rollout_batch(
    *,
    sample_count: int = 96,
    horizon: int = 4,
    latent_dim: int = 3,
    action_dim: int = 2,
    seed: int = 1729,
    split: str = "smoke",
) -> LatentRolloutBatch:
    if sample_count < 1:
        raise ValueError("sample_count must be positive")
    if horizon < 1:
        raise ValueError("horizon must be positive")
    rng = np.random.default_rng(seed)
    initial = rng.normal(0.0, 0.7, size=(sample_count, latent_dim))
    actions = rng.normal(0.0, 0.35, size=(sample_count, horizon, action_dim))
    transition = np.array(
        [
            [0.82, 0.06, -0.02],
            [0.03, 0.76, 0.05],
            [0.04, -0.03, 0.70],
        ],
        dtype=np.float64,
    )
    action_map = np.array(
        [
            [0.22, -0.07, 0.04],
            [-0.04, 0.18, 0.11],
        ],
        dtype=np.float64,
    )
    if latent_dim != 3 or action_dim != 2:
        transition = np.eye(latent_dim, dtype=np.float64) * 0.75
        action_map = rng.normal(0.0, 0.12, size=(action_dim, latent_dim))
    latents = np.empty((sample_count, horizon, latent_dim), dtype=np.float64)
    state = initial.copy()
    unsafe = np.zeros((sample_count, horizon), dtype=bool)
    for step in range(horizon):
        state = state @ transition.T + actions[:, step, :] @ action_map
        latents[:, step, :] = state
        unsafe[:, step] = np.linalg.norm(state, axis=1) > 1.6
    return LatentRolloutBatch(
        environment_id="boundary-gated-ou-latent-rollout",
        split=split,
        horizon=horizon,
        initial_latents=initial,
        actions=actions,
        target_latents=latents,
        unsafe_transition=unsafe,
    )


def _specs_for_batch(batch: LatentRolloutBatch) -> list[PredictorSpec]:
    latent_dim = int(batch.initial_latents.shape[1])
    action_dim = int(batch.actions.shape[2])
    return [
        PredictorSpec(
            predictor_id="one_step_jepa_mlp_smoke",
            family="jepa_mlp",
            latent_dim=latent_dim,
            action_dim=action_dim,
            horizon=1,
            lambda_gap=0.5,
            lambda_latent=1.0,
            action_conditioned=True,
            training_status="deterministic_smoke_baseline",
            fit_method="closed local action-conditioned projection",
        ),
        PredictorSpec(
            predictor_id="k_step_jepa_mlp_smoke",
            family="jepa_mlp",
            latent_dim=latent_dim,
            action_dim=action_dim,
            horizon=int(batch.horizon),
            lambda_gap=0.5,
            lambda_latent=1.0,
            action_conditioned=True,
            training_status="deterministic_smoke_baseline",
            fit_method="closed local action-conditioned projection",
        ),
        PredictorSpec(
            predictor_id="gru_rollout_smoke",
            family="gru",
            latent_dim=latent_dim,
            action_dim=action_dim,
            horizon=int(batch.horizon),
            lambda_gap=1.0,
            lambda_latent=1.0,
            action_conditioned=True,
            training_status="deterministic_smoke_baseline",
            fit_method="closed local recurrent surrogate",
        ),
        PredictorSpec(
            predictor_id="rssm_rollout_smoke",
            family="rssm",
            latent_dim=latent_dim,
            action_dim=action_dim,
            horizon=int(batch.horizon),
            lambda_gap=1.0,
            lambda_latent=0.75,
            action_conditioned=True,
            training_status="deterministic_smoke_baseline",
            fit_method="closed local state-space surrogate",
        ),
        PredictorSpec(
            predictor_id="transformer_rollout_smoke",
            family="transformer",
            latent_dim=latent_dim,
            action_dim=action_dim,
            horizon=int(batch.horizon),
            lambda_gap=0.75,
            lambda_latent=1.0,
            action_conditioned=True,
            training_status="deterministic_smoke_baseline",
            fit_method="closed local sequence surrogate",
        ),
    ]


def _predict_persistence(batch: LatentRolloutBatch, spec: PredictorSpec) -> np.ndarray:
    repeated = np.repeat(batch.initial_latents[:, None, :], batch.horizon, axis=1)
    cumulative_actions = np.cumsum(batch.actions, axis=1)
    action_projection = np.zeros_like(repeated)
    cols = min(cumulative_actions.shape[2], action_projection.shape[2])
    family_scale = {
        "jepa_mlp": 0.15,
        "gru": 0.18,
        "rssm": 0.20,
        "transformer": 0.17,
    }.get(spec.family, 0.15)
    if spec.action_conditioned:
        action_projection[:, :, :cols] = family_scale * cumulative_actions[:, :, :cols]
    inertia = 0.90 if spec.family == "rssm" else 0.86
    trend = np.arange(1, batch.horizon + 1, dtype=np.float64)[None, :, None]
    predicted = repeated * (inertia ** trend) + action_projection
    if spec.horizon == 1:
        predicted[:, 1:, :] = predicted[:, :1, :]
    return predicted


def _latent_score(predicted: np.ndarray, target: np.ndarray) -> float:
    residual = predicted - target
    mse = float(np.mean(residual * residual))
    target_energy = float(np.mean(target * target))
    return float(max(0.0, min(1.0, 1.0 - mse / max(target_energy, 1e-12))))


def _run_record(batch: LatentRolloutBatch, spec: PredictorSpec) -> dict[str, Any]:
    predicted = _predict_persistence(batch, spec)
    target = batch.target_latents
    rollout_mse = float(np.mean((predicted - target) ** 2))
    latent_r2_1step = _latent_score(predicted[:, :1, :], target[:, :1, :])
    latent_r2_kstep = _latent_score(predicted, target)
    terminal_unsafe = batch.unsafe_transition[:, -1]
    predicted_radius = np.linalg.norm(predicted[:, -1, :], axis=1)
    if np.any(terminal_unsafe) and np.any(~terminal_unsafe):
        safe_margin = float(np.mean(predicted_radius[terminal_unsafe]) - np.mean(predicted_radius[~terminal_unsafe]))
        gap_detection_auc_value = float(max(0.0, min(1.0, 0.5 + 0.25 * safe_margin)))
    else:
        gap_detection_auc_value = 0.5
    coverage = float(1.0 - np.mean(batch.unsafe_transition))
    unlogged_error = float(np.mean((predicted_radius > 1.7) & (~terminal_unsafe)))
    return {
        "predictor_id": spec.predictor_id,
        "family": spec.family,
        "horizon": int(spec.horizon),
        "lambda_gap": float(spec.lambda_gap),
        "lambda_latent": float(spec.lambda_latent),
        "action_conditioned": bool(spec.action_conditioned),
        "latent_r2_1step": latent_r2_1step,
        "latent_r2_kstep": latent_r2_kstep,
        "rollout_mse": rollout_mse,
        "gap_detection_auc": gap_detection_auc_value,
        "certified_coverage": coverage,
        "unlogged_error_rate": unlogged_error,
        "planning_success": None,
    }


def _summary(runs: list[dict[str, Any]]) -> dict[str, Any]:
    if not runs:
        return {
            "run_count": 0,
            "family_count": 0,
            "best_latent_r2_kstep": 0.0,
            "mean_rollout_mse": 0.0,
            "min_gap_detection_auc": 0.0,
            "min_certified_coverage": 0.0,
            "max_unlogged_error_rate": 0.0,
            "planning_success_claimed": False,
        }
    return {
        "run_count": int(len(runs)),
        "family_count": int(len({str(run["family"]) for run in runs})),
        "best_latent_r2_kstep": float(max(float(run["latent_r2_kstep"]) for run in runs)),
        "mean_rollout_mse": float(np.mean([float(run["rollout_mse"]) for run in runs])),
        "min_gap_detection_auc": float(min(float(run["gap_detection_auc"]) for run in runs)),
        "min_certified_coverage": float(min(float(run["certified_coverage"]) for run in runs)),
        "max_unlogged_error_rate": float(max(float(run["unlogged_error_rate"]) for run in runs)),
        "planning_success_claimed": any(run["planning_success"] is not None for run in runs),
    }


def run_multistep_latent_prediction_smoke(
    *,
    sample_count: int = 96,
    horizon: int = 4,
    seed: int = 1729,
) -> dict[str, Any]:
    batch = make_latent_rollout_batch(sample_count=sample_count, horizon=horizon, seed=seed)
    predictor_specs = _specs_for_batch(batch)
    runs = [_run_record(batch, spec) for spec in predictor_specs]
    summary = _summary(runs)
    gate = LatentPredictionGateSpec(
        gate_id="latent-rollout-smoke-nonblocking",
        min_gap_detection_auc=0.45,
        min_certified_coverage=0.50,
        max_unlogged_error_rate=0.20,
        min_coverage=0.50,
        required_record_fields=(
            "rollout_contract",
            "predictor_specs",
            "hardgate",
            "runs",
            "summary",
            "metrics",
            "cannot_claim",
        ),
    )
    gate_record = gate.evaluate(runs)
    metrics = {
        "latent_prediction_score": float(summary["best_latent_r2_kstep"]),
        "rollout_mse": float(summary["mean_rollout_mse"]),
        "gap_detection_auc": float(summary["min_gap_detection_auc"]),
        "certified_coverage": float(summary["min_certified_coverage"]),
        "unlogged_error_rate": float(summary["max_unlogged_error_rate"]),
    }
    return {
        "schema_id": "bedc-multistep-latent-prediction",
        "status": "executed",
        "record_scope": "local_smoke_contract",
        "experiment_contract": {
            "objective": "compare action-conditioned one-step and K-step latent rollout predictors on one local evidence surface",
            "execution_scope": "deterministic CPU smoke record",
            "nonblocking_readiness": True,
        },
        "rollout_contract": batch.to_record(),
        "predictor_specs": [spec.to_record() for spec in predictor_specs],
        "hardgate": gate_record,
        "runs": runs,
        "summary": summary,
        "metrics": metrics,
        "execution_contract": {
            "default_command": "python scripts/run_bedc_multistep_latent_prediction.py",
            "default_report": "reports/bedc_multistep_latent_prediction.json",
            "saves_per_example_latents": False,
        },
        "evidence_chain": {
            "owner_module": "bedc_quality_lab.bedc_multistep_latent_prediction",
            "manifest_key": "multistep_latent_prediction",
            "readiness_contract": "multistep_latent_prediction",
        },
        "claim_scope": {
            "local_latent_rollout_smoke": gate_record["status"],
            "minigrid_planning_success": "not_claimed",
            "native_vjepa2_ac_rollout": "not_claimed",
            "full_4090_sweep": "not_claimed",
        },
        "cannot_claim": [
            "MiniGrid planning success",
            "public benchmark superiority",
            "native V-JEPA2-AC rollout reproduction",
            "quality backend full-sweep admission",
        ],
    }


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
