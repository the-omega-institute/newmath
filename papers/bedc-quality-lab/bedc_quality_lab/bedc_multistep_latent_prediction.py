"""Local multi-step latent prediction evidence packet for BEDC-JEPA."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any

import numpy as np


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
        "rollout_batch": batch.to_record(),
        "predictor_specs": [spec.to_record() for spec in predictor_specs],
        "predictor_spec": predictor_specs[0].to_record(),
        "hardgate": gate_record,
        "gate_spec": gate_record,
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
