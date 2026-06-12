#!/usr/bin/env python3
"""Run a Gaussian-OU BEDC-JEPA dynamics and gap-aware planning experiment."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from itertools import product
import json
import math
from pathlib import Path
import sys
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.toy_world import make_toy_batch
from scripts.experiment_stats import metric_stats
from scripts.run_gaussian_ou_distinction_head import (
    DISTINCTIONS,
    _high_energy_threshold,
    _label_truth,
    _seeds,
    _train_eval_split,
)
from scripts.run_gaussian_ou_lejepa import run_experiment


SAMPLE_COUNT = 384
SEED_COUNT = 30
RHO = 0.82
USE_TORCH = False
TRAIN_FRACTION = 0.70
PLANNER_HORIZON = 3
EVAL_START_COUNT = 64
LAMBDA_GRID = (0.0, 0.25, 0.5, 1.0, 2.0)
PRIMARY_LAMBDA = 1.0
GAP_THRESHOLD = 0.45
ERROR_THRESHOLD = 0.22
RIDGE = 1.0e-3
JSON_ARTIFACT = "reports/gaussian_ou_dynamics_planning.json"
REPORT_ARTIFACT = "reports/gaussian_ou_dynamics_planning.md"
TARGET = np.array([1.35, 1.05], dtype=np.float64)
START_CENTER = np.array([-1.15, -0.85], dtype=np.float64)
HAZARD_CENTER = np.array([0.08, 0.06], dtype=np.float64)
HAZARD_RADIUS = 0.54
COLLISION_RADIUS = 0.36
WORLD_BOUND = 2.75
ACTION_SET = (
    (0.0, 0.0),
    (0.62, 0.0),
    (0.0, 0.62),
    (0.44, 0.44),
    (0.62, 0.34),
)
ARM_ORDER = (
    "vanilla_jepa",
    "jepa_posthoc_probe",
    "jepa_posthoc_bedc_report",
    "bedc_jepa_end_to_end",
)
ARM_LABELS = {
    "vanilla_jepa": "Vanilla JEPA",
    "jepa_posthoc_probe": "JEPA + post-hoc probe",
    "jepa_posthoc_bedc_report": "JEPA + post-hoc BEDC report",
    "bedc_jepa_end_to_end": "BEDC-JEPA end-to-end",
}
EPS = 1.0e-12


@dataclass(frozen=True)
class ArmConfig:
    name: str
    uses_distinction_input: bool
    uses_gap_input: bool
    predicts_distinction: bool
    predicts_gap: bool
    report_gap: bool
    gap_weighted_fit: bool
    gap_penalty_enabled: bool


@dataclass(frozen=True)
class DynamicsModel:
    arm: str
    weights: np.ndarray
    output_dim: int
    z_slice: slice
    d_slice: slice | None
    g_slice: slice | None
    x_mean: np.ndarray
    x_scale: np.ndarray
    y_mean: np.ndarray
    y_scale: np.ndarray
    train_latent_mse: float


ARM_CONFIGS = {
    "vanilla_jepa": ArmConfig(
        name="vanilla_jepa",
        uses_distinction_input=False,
        uses_gap_input=False,
        predicts_distinction=False,
        predicts_gap=False,
        report_gap=False,
        gap_weighted_fit=False,
        gap_penalty_enabled=False,
    ),
    "jepa_posthoc_probe": ArmConfig(
        name="jepa_posthoc_probe",
        uses_distinction_input=True,
        uses_gap_input=False,
        predicts_distinction=True,
        predicts_gap=False,
        report_gap=False,
        gap_weighted_fit=False,
        gap_penalty_enabled=False,
    ),
    "jepa_posthoc_bedc_report": ArmConfig(
        name="jepa_posthoc_bedc_report",
        uses_distinction_input=True,
        uses_gap_input=False,
        predicts_distinction=True,
        predicts_gap=False,
        report_gap=True,
        gap_weighted_fit=False,
        gap_penalty_enabled=True,
    ),
    "bedc_jepa_end_to_end": ArmConfig(
        name="bedc_jepa_end_to_end",
        uses_distinction_input=True,
        uses_gap_input=True,
        predicts_distinction=True,
        predicts_gap=True,
        report_gap=False,
        gap_weighted_fit=True,
        gap_penalty_enabled=True,
    ),
}


def _require_finite(name: str, array: np.ndarray, *, ndim: int | None = None) -> np.ndarray:
    value = np.asarray(array, dtype=np.float64)
    if ndim is not None and value.ndim != ndim:
        raise ValueError(f"{name} must have ndim {ndim}")
    if value.size == 0:
        raise ValueError(f"{name} must not be empty")
    if not np.all(np.isfinite(value)):
        raise ValueError(f"{name} contains non-finite values")
    return value


def _action_array() -> np.ndarray:
    return np.asarray(ACTION_SET, dtype=np.float64)


def _state_distinctions(z: np.ndarray, *, high_energy_threshold: float) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    return np.column_stack(
        [
            _label_truth(name, z, high_energy_threshold=high_energy_threshold)
            for name in DISTINCTIONS
        ]
    ).astype(np.float64)


def _hazard_distance(z: np.ndarray) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    return np.linalg.norm(z - HAZARD_CENTER.reshape(1, 2), axis=1)


def _unsafe_state(z: np.ndarray) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    hazard = _hazard_distance(z) <= HAZARD_RADIUS
    out_of_bounds = np.max(np.abs(z), axis=1) > WORLD_BOUND
    return np.logical_or(hazard, out_of_bounds)


def _segment_distance_to_hazard(z0: np.ndarray, z1: np.ndarray) -> np.ndarray:
    z0 = _require_finite("z0", z0, ndim=2)
    z1 = _require_finite("z1", z1, ndim=2)
    segment = z1 - z0
    center = HAZARD_CENTER.reshape(1, 2)
    denom = np.sum(segment * segment, axis=1)
    raw_t = np.sum((center - z0) * segment, axis=1) / np.maximum(denom, EPS)
    t = np.clip(raw_t, 0.0, 1.0).reshape(-1, 1)
    closest = z0 + t * segment
    return np.linalg.norm(closest - center, axis=1)


def _collision(z0: np.ndarray, z1: np.ndarray) -> np.ndarray:
    return _segment_distance_to_hazard(z0, z1) <= COLLISION_RADIUS


def _target_cost(z: np.ndarray, action: np.ndarray) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    action = _require_finite("action", action, ndim=2)
    distance_cost = np.sum(np.square(z - TARGET.reshape(1, 2)), axis=1)
    action_cost = 0.035 * np.sum(np.square(action), axis=1)
    hazard_margin = np.maximum(0.0, HAZARD_RADIUS + 0.22 - _hazard_distance(z))
    return distance_cost + action_cost + 4.0 * np.square(hazard_margin)


def _true_next_z(z: np.ndarray, action: np.ndarray) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    action = _require_finite("action", action, ndim=2)
    if z.shape != action.shape:
        raise ValueError("z and action must have the same shape")
    dist = _hazard_distance(z).reshape(-1, 1)
    hazard_gate = np.exp(-np.square(dist / 0.72))
    shear = np.column_stack(
        [
            0.09 * np.sin(1.8 * z[:, 1]),
            -0.07 * np.sin(1.4 * z[:, 0]),
        ]
    )
    slip = hazard_gate * np.column_stack(
        [
            -0.38 * action[:, 1] + 0.13,
            0.34 * action[:, 0] - 0.10,
        ]
    )
    return (0.79 * z + action + shear + slip).astype(np.float64)


def _gap_signal(
    z: np.ndarray,
    d: np.ndarray,
    *,
    center: np.ndarray,
    radius_scale: float,
    training_residual: np.ndarray | None = None,
) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    d = _require_finite("d", d, ndim=2)
    if d.shape[0] != z.shape[0]:
        raise ValueError("d must align with z")
    center = _require_finite("center", center.reshape(1, -1), ndim=2).reshape(-1)
    radius = float(max(radius_scale, EPS))
    ood = np.maximum(0.0, (np.linalg.norm(z - center.reshape(1, 2), axis=1) - radius) / radius)
    hazard_band = np.exp(-np.square((_hazard_distance(z) - HAZARD_RADIUS) / 0.35))
    low_margin = np.mean(1.0 - np.abs(2.0 * d - 1.0), axis=1)
    residual = np.zeros(z.shape[0], dtype=np.float64)
    if training_residual is not None:
        residual = np.asarray(training_residual, dtype=np.float64)
        if residual.shape != (z.shape[0],):
            raise ValueError("training_residual must align with z")
    raw = 0.52 * hazard_band + 0.28 * np.clip(ood, 0.0, 2.0) + 0.16 * low_margin + 0.34 * residual
    return np.clip(raw, 0.0, 1.0).reshape(-1, 1).astype(np.float64)


def _report_gap_signal(z: np.ndarray, d: np.ndarray, *, center: np.ndarray, radius_scale: float) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    d = _require_finite("d", d, ndim=2)
    radius = float(max(radius_scale, EPS))
    ood = np.maximum(0.0, (np.linalg.norm(z - center.reshape(1, 2), axis=1) - radius) / radius)
    hazard_band = np.exp(-np.square((_hazard_distance(z) - HAZARD_RADIUS) / 0.48))
    low_margin = np.mean(1.0 - np.abs(2.0 * d - 1.0), axis=1)
    raw = 0.28 * hazard_band + 0.16 * np.clip(ood, 0.0, 2.0) + 0.10 * low_margin
    return np.clip(raw, 0.0, 1.0).reshape(-1, 1).astype(np.float64)


def _all_action_sequences() -> np.ndarray:
    actions = _action_array()
    indexes = np.asarray(list(product(range(len(actions)), repeat=PLANNER_HORIZON)), dtype=np.int64)
    return actions[indexes]


def _feature_matrix(z: np.ndarray, d: np.ndarray, g: np.ndarray, action: np.ndarray, config: ArmConfig) -> np.ndarray:
    z = _require_finite("z", z, ndim=2)
    d = _require_finite("d", d, ndim=2)
    g = _require_finite("g", g, ndim=2)
    action = _require_finite("action", action, ndim=2)
    if not (z.shape[0] == d.shape[0] == g.shape[0] == action.shape[0]):
        raise ValueError("feature inputs must align")
    parts = [
        z,
        action,
        z * action,
        np.square(z),
        np.sin(z),
        np.ones((z.shape[0], 1), dtype=np.float64),
    ]
    if config.uses_distinction_input:
        parts.extend([d, d * g])
    if config.uses_gap_input:
        parts.extend([g, g * action[:, :1], g * z])
    return np.column_stack(parts).astype(np.float64)


def _output_matrix(z_next: np.ndarray, d_next: np.ndarray, g_next: np.ndarray, config: ArmConfig) -> tuple[np.ndarray, slice, slice | None, slice | None]:
    parts = [z_next]
    z_slice = slice(0, 2)
    cursor = 2
    d_slice = None
    g_slice = None
    if config.predicts_distinction:
        d_slice = slice(cursor, cursor + d_next.shape[1])
        parts.append(d_next)
        cursor += d_next.shape[1]
    if config.predicts_gap:
        g_slice = slice(cursor, cursor + 1)
        parts.append(g_next)
    return np.column_stack(parts).astype(np.float64), z_slice, d_slice, g_slice


def _standardize_fit(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    x = _require_finite("x", x, ndim=2)
    mean = np.mean(x, axis=0, keepdims=True)
    scale = np.std(x, axis=0, keepdims=True)
    scale = np.where(scale <= EPS, 1.0, scale)
    return mean, scale


def _fit_dynamics_model(
    *,
    z: np.ndarray,
    d: np.ndarray,
    g: np.ndarray,
    actions: np.ndarray,
    z_next: np.ndarray,
    d_next: np.ndarray,
    g_next: np.ndarray,
    config: ArmConfig,
) -> DynamicsModel:
    x = _feature_matrix(z, d, g, actions, config)
    y, z_slice, d_slice, g_slice = _output_matrix(z_next, d_next, g_next, config)
    x_mean, x_scale = _standardize_fit(x)
    y_mean, y_scale = _standardize_fit(y)
    xs = (x - x_mean) / x_scale
    ys = (y - y_mean) / y_scale
    if config.gap_weighted_fit:
        weights = (1.0 + 2.2 * g[:, 0] + 1.2 * _unsafe_state(z_next).astype(np.float64)).reshape(-1, 1)
    else:
        weights = np.ones((x.shape[0], 1), dtype=np.float64)
    xw = xs * np.sqrt(weights)
    yw = ys * np.sqrt(weights)
    gram = xw.T @ xw + RIDGE * np.eye(xw.shape[1], dtype=np.float64)
    coef = np.linalg.solve(gram, xw.T @ yw)
    pred = ((xs @ coef) * y_scale) + y_mean
    train_latent_mse = float(np.mean(np.sum(np.square(pred[:, z_slice] - z_next), axis=1)))
    return DynamicsModel(
        arm=config.name,
        weights=coef,
        output_dim=y.shape[1],
        z_slice=z_slice,
        d_slice=d_slice,
        g_slice=g_slice,
        x_mean=x_mean,
        x_scale=x_scale,
        y_mean=y_mean,
        y_scale=y_scale,
        train_latent_mse=train_latent_mse,
    )


def _predict_dynamics(
    model: DynamicsModel,
    z: np.ndarray,
    d: np.ndarray,
    g: np.ndarray,
    action: np.ndarray,
    config: ArmConfig,
    *,
    gap_center: np.ndarray,
    gap_radius: float,
) -> dict[str, np.ndarray]:
    x = _feature_matrix(z, d, g, action, config)
    xs = (x - model.x_mean) / model.x_scale
    y = ((xs @ model.weights) * model.y_scale) + model.y_mean
    z_pred = y[:, model.z_slice]
    if model.d_slice is not None:
        d_pred = np.clip(y[:, model.d_slice], 0.0, 1.0)
    else:
        d_pred = _state_distinctions(z_pred, high_energy_threshold=0.0)
    if model.g_slice is not None:
        g_pred = np.clip(y[:, model.g_slice], 0.0, 1.0)
    elif config.report_gap:
        g_pred = _report_gap_signal(z_pred, d_pred, center=gap_center, radius_scale=gap_radius)
    else:
        g_pred = np.zeros((z_pred.shape[0], 1), dtype=np.float64)
    return {"z": z_pred.astype(np.float64), "d": d_pred.astype(np.float64), "g": g_pred.astype(np.float64)}


def _rollout_predicted(
    model: DynamicsModel,
    start_z: np.ndarray,
    start_d: np.ndarray,
    start_g: np.ndarray,
    sequences: np.ndarray,
    config: ArmConfig,
    *,
    gap_center: np.ndarray,
    gap_radius: float,
) -> dict[str, np.ndarray]:
    sequences = _require_finite("sequences", sequences)
    if sequences.ndim != 3 or sequences.shape[1:] != (PLANNER_HORIZON, 2):
        raise ValueError("sequences must have shape (m, horizon, 2)")
    count = sequences.shape[0]
    z = np.repeat(start_z.reshape(1, 2), count, axis=0)
    d = np.repeat(start_d.reshape(1, start_d.shape[0]), count, axis=0)
    g = np.repeat(start_g.reshape(1, 1), count, axis=0)
    zs = []
    gs = []
    step_costs = []
    for step in range(PLANNER_HORIZON):
        action = sequences[:, step, :]
        pred = _predict_dynamics(
            model,
            z,
            d,
            g,
            action,
            config,
            gap_center=gap_center,
            gap_radius=gap_radius,
        )
        z = pred["z"]
        d = pred["d"]
        g = pred["g"]
        zs.append(z)
        gs.append(g)
        step_costs.append(_target_cost(z, action))
    return {
        "z": np.stack(zs, axis=1),
        "g": np.stack(gs, axis=1),
        "cost": np.sum(np.stack(step_costs, axis=1), axis=1),
    }


def _rollout_truth(start_z: np.ndarray, sequence: np.ndarray, *, high_energy_threshold: float, gap_center: np.ndarray, gap_radius: float) -> dict[str, Any]:
    sequence = _require_finite("sequence", sequence, ndim=2)
    z = start_z.reshape(1, 2)
    states = []
    gaps = []
    costs = []
    unsafe = False
    collision = False
    for action in sequence:
        action_row = action.reshape(1, 2)
        z_next = _true_next_z(z, action_row)
        d_next = _state_distinctions(z_next, high_energy_threshold=high_energy_threshold)
        g_next = _gap_signal(z_next, d_next, center=gap_center, radius_scale=gap_radius)
        unsafe = bool(unsafe or bool(_unsafe_state(z_next)[0]))
        collision = bool(collision or bool(_collision(z, z_next)[0]))
        costs.append(float(_target_cost(z_next, action_row)[0]))
        states.append(z_next.reshape(2))
        gaps.append(float(g_next[0, 0]))
        z = z_next
    final_z = states[-1]
    initial_distance = float(np.linalg.norm(start_z - TARGET))
    final_distance = float(np.linalg.norm(final_z - TARGET))
    task_progress = initial_distance - final_distance
    planner_success = bool(task_progress >= 0.18 and not unsafe and not collision)
    return {
        "states": [state.tolist() for state in states],
        "gap_scores": gaps,
        "unsafe_state": unsafe,
        "collision": collision,
        "task_progress": float(task_progress),
        "final_distance": float(final_distance),
        "cost": float(sum(costs)),
        "planner_success": planner_success,
    }


def _plan(
    model: DynamicsModel,
    start_z: np.ndarray,
    start_d: np.ndarray,
    start_g: np.ndarray,
    config: ArmConfig,
    *,
    lambda_gap: float,
    gap_center: np.ndarray,
    gap_radius: float,
) -> dict[str, Any]:
    sequences = _all_action_sequences()
    predicted = _rollout_predicted(
        model,
        start_z,
        start_d,
        start_g,
        sequences,
        config,
        gap_center=gap_center,
        gap_radius=gap_radius,
    )
    predicted_cost = predicted["cost"]
    gap_l1 = np.sum(np.abs(predicted["g"][:, :, 0]), axis=1)
    penalty = float(lambda_gap) * gap_l1 if config.gap_penalty_enabled else np.zeros_like(gap_l1)
    objective = predicted_cost + penalty
    index = int(np.argmin(objective))
    return {
        "sequence": sequences[index],
        "predicted_cost": float(predicted_cost[index]),
        "predicted_gap_l1": float(gap_l1[index]),
        "objective": float(objective[index]),
        "enumerated_sequence_count": int(sequences.shape[0]),
        "predicted_final_z": predicted["z"][index, -1, :].tolist(),
        "predicted_path_gap": [float(value) for value in predicted["g"][index, :, 0]],
    }


def _oracle_plan(start_z: np.ndarray, *, high_energy_threshold: float, gap_center: np.ndarray, gap_radius: float) -> dict[str, Any]:
    best_index = 0
    best_score = math.inf
    best_truth: dict[str, Any] | None = None
    sequences = _all_action_sequences()
    for index, sequence in enumerate(sequences):
        truth = _rollout_truth(
            start_z,
            sequence,
            high_energy_threshold=high_energy_threshold,
            gap_center=gap_center,
            gap_radius=gap_radius,
        )
        safety_penalty = 100.0 * float(truth["unsafe_state"] or truth["collision"])
        score = float(truth["cost"]) + safety_penalty
        if score < best_score:
            best_score = score
            best_index = index
            best_truth = truth
    assert best_truth is not None
    return {
        "sequence": sequences[best_index],
        "score": float(best_score),
        "cost": float(best_truth["cost"]),
        "planner_success": bool(best_truth["planner_success"]),
    }


def _train_transitions(seed: int, z: np.ndarray, train_idx: np.ndarray, *, high_energy_threshold: float) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed ^ 0xD17A)
    actions = _action_array()
    repeats = np.tile(actions, (len(train_idx), 1))
    bases = np.repeat(z[train_idx], len(actions), axis=0)
    jitter = rng.normal(scale=0.015, size=bases.shape)
    bases = bases + jitter
    z_next = _true_next_z(bases, repeats)
    d = _state_distinctions(bases, high_energy_threshold=high_energy_threshold)
    d_next = _state_distinctions(z_next, high_energy_threshold=high_energy_threshold)
    center = np.mean(z[train_idx], axis=0)
    radius = float(np.quantile(np.linalg.norm(z[train_idx] - center.reshape(1, 2), axis=1), 0.82))
    base_residual = _collision(bases, z_next).astype(np.float64) * 0.5
    g = _gap_signal(bases, d, center=center, radius_scale=radius, training_residual=base_residual)
    next_residual = _collision(bases, z_next).astype(np.float64) * 0.75
    g_next = _gap_signal(z_next, d_next, center=center, radius_scale=radius, training_residual=next_residual)
    return {
        "z": bases,
        "d": d,
        "g": g,
        "action": repeats,
        "z_next": z_next,
        "d_next": d_next,
        "g_next": g_next,
        "gap_center": center,
        "gap_radius": np.array([radius], dtype=np.float64),
    }


def _start_indices(z: np.ndarray, eval_idx: np.ndarray) -> np.ndarray:
    candidates = z[eval_idx]
    distances = np.linalg.norm(candidates - START_CENTER.reshape(1, 2), axis=1)
    order = np.argsort(distances)
    return np.sort(eval_idx[order[: min(EVAL_START_COUNT, len(order))]])


def _calibration_auc(labels: list[float], scores: list[float]) -> float:
    y = np.asarray(labels, dtype=np.float64)
    s = np.asarray(scores, dtype=np.float64)
    pos = s[y >= 0.5]
    neg = s[y < 0.5]
    if pos.size == 0 or neg.size == 0:
        return math.nan
    wins = 0.0
    for value in pos:
        wins += float(np.sum(value > neg)) + 0.5 * float(np.sum(value == neg))
    return float(wins / (pos.size * neg.size))


def _calibration_ece(labels: list[float], scores: list[float], *, bins: int = 8) -> float:
    y = np.asarray(labels, dtype=np.float64)
    s = np.clip(np.asarray(scores, dtype=np.float64), 0.0, 1.0)
    if y.size == 0:
        return math.nan
    total = float(y.size)
    ece = 0.0
    edges = np.linspace(0.0, 1.0, bins + 1)
    for index in range(bins):
        if index == bins - 1:
            mask = (s >= edges[index]) & (s <= edges[index + 1])
        else:
            mask = (s >= edges[index]) & (s < edges[index + 1])
        if not np.any(mask):
            continue
        ece += float(np.sum(mask)) / total * abs(float(np.mean(s[mask])) - float(np.mean(y[mask])))
    return float(ece)


def _seed_context(seed: int, seed_index: int) -> dict[str, Any]:
    batch = make_toy_batch(SAMPLE_COUNT, rho=RHO, seed=seed)
    z = _require_finite("z", batch.z, ndim=2)
    train_idx, eval_idx = _train_eval_split(z.shape[0], seed=seed)
    high_threshold = _high_energy_threshold(z, train_idx)
    transitions = _train_transitions(seed, z, train_idx, high_energy_threshold=high_threshold)
    starts = _start_indices(z, eval_idx)
    envelope = run_experiment(
        use_torch=USE_TORCH,
        sample_count=SAMPLE_COUNT,
        seed=seed,
        rho=RHO,
        run_id=f"gaussian-ou-dynamics-planning-seed-{seed}",
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    return {
        "seed": int(seed),
        "seed_index": int(seed_index),
        "z": z,
        "train_idx": train_idx,
        "eval_idx": eval_idx,
        "starts": starts,
        "high_energy_threshold": high_threshold,
        "transitions": transitions,
        "canonical_envelope_projection": {
            "run_id": envelope.run_id,
            "source_spec": dict(envelope.source_spec),
            "classifier_spec": dict(envelope.classifier_spec),
            "metrics": {name: float(value) for name, value in envelope.metrics.items()},
            "artifacts": dict(envelope.artifacts),
        },
    }


def _fit_arm_models(context: dict[str, Any]) -> dict[str, DynamicsModel]:
    transitions = context["transitions"]
    models = {}
    for arm in ARM_ORDER:
        config = ARM_CONFIGS[arm]
        models[arm] = _fit_dynamics_model(
            z=transitions["z"],
            d=transitions["d"],
            g=transitions["g"],
            actions=transitions["action"],
            z_next=transitions["z_next"],
            d_next=transitions["d_next"],
            g_next=transitions["g_next"],
            config=config,
        )
    return models


def _evaluate_seed(context: dict[str, Any], models: dict[str, DynamicsModel]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    z = context["z"]
    high_threshold = float(context["high_energy_threshold"])
    transitions = context["transitions"]
    gap_center = transitions["gap_center"]
    gap_radius = float(transitions["gap_radius"][0])
    start_rows = []
    for start_index in context["starts"]:
        start_z = z[int(start_index)]
        start_d = _state_distinctions(start_z.reshape(1, 2), high_energy_threshold=high_threshold)[0]
        start_g = _gap_signal(
            start_z.reshape(1, 2),
            start_d.reshape(1, len(DISTINCTIONS)),
            center=gap_center,
            radius_scale=gap_radius,
        )[0]
        oracle = _oracle_plan(
            start_z,
            high_energy_threshold=high_threshold,
            gap_center=gap_center,
            gap_radius=gap_radius,
        )
        start_rows.append((int(start_index), start_z, start_d, start_g, oracle))

    for arm in ARM_ORDER:
        config = ARM_CONFIGS[arm]
        model = models[arm]
        for lambda_gap in LAMBDA_GRID:
            per_start = []
            for start_index, start_z, start_d, start_g, oracle in start_rows:
                plan = _plan(
                    model,
                    start_z,
                    start_d,
                    start_g,
                    config,
                    lambda_gap=float(lambda_gap),
                    gap_center=gap_center,
                    gap_radius=gap_radius,
                )
                truth = _rollout_truth(
                    start_z,
                    plan["sequence"],
                    high_energy_threshold=high_threshold,
                    gap_center=gap_center,
                    gap_radius=gap_radius,
                )
                prediction_error = float(np.linalg.norm(np.asarray(plan["predicted_final_z"]) - np.asarray(truth["states"][-1])))
                gap_score = float(max(plan["predicted_path_gap"]) if plan["predicted_path_gap"] else 0.0)
                unlogged = bool(prediction_error > ERROR_THRESHOLD and gap_score < GAP_THRESHOLD)
                planning_regret = float(truth["cost"] - oracle["cost"])
                safe_planning_success = bool(truth["planner_success"] and not truth["unsafe_state"] and not truth["collision"])
                per_start.append(
                    {
                        "start_state_id": int(start_index),
                        "chosen_action_sequence": np.asarray(plan["sequence"], dtype=np.float64).tolist(),
                        "predicted_cost": float(plan["predicted_cost"]),
                        "predicted_gap_l1": float(plan["predicted_gap_l1"]),
                        "objective": float(plan["objective"]),
                        "predicted_final_z": plan["predicted_final_z"],
                        "predicted_path_gap": plan["predicted_path_gap"],
                        "truth_rollout": truth,
                        "oracle_cost": float(oracle["cost"]),
                        "oracle_score": float(oracle["score"]),
                        "chosen_cost": float(truth["cost"]),
                        "planning_regret": planning_regret,
                        "prediction_error": prediction_error,
                        "gap_score": gap_score,
                        "unlogged_error": unlogged,
                        "gap_event": bool(unlogged or truth["unsafe_state"] or truth["collision"]),
                        "unsafe_state": bool(truth["unsafe_state"]),
                        "collision": bool(truth["collision"]),
                        "safe_planning_success": safe_planning_success,
                    }
                )
            records.append(_summarize_record(context, arm, lambda_gap, model, per_start))
    return records


def _summarize_record(
    context: dict[str, Any],
    arm: str,
    lambda_gap: float,
    model: DynamicsModel,
    per_start: list[dict[str, Any]],
) -> dict[str, Any]:
    unsafe_values = [float(row["unsafe_state"]) for row in per_start]
    collision_values = [float(row["collision"]) for row in per_start]
    success_values = [float(row["safe_planning_success"]) for row in per_start]
    unlogged_values = [float(row["unlogged_error"]) for row in per_start]
    regret_values = [float(row["planning_regret"]) for row in per_start]
    prediction_errors = [float(row["prediction_error"]) for row in per_start]
    gap_scores = [float(row["gap_score"]) for row in per_start]
    gap_events = [float(row["gap_event"]) for row in per_start]
    audit_rows = [
        {
            "start_state_id": int(row["start_state_id"]),
            "chosen_action_sequence": row["chosen_action_sequence"],
            "unsafe_state": bool(row["unsafe_state"]),
            "collision": bool(row["collision"]),
            "safe_planning_success": bool(row["safe_planning_success"]),
            "planning_regret": float(row["planning_regret"]),
            "prediction_error": float(row["prediction_error"]),
            "gap_score": float(row["gap_score"]),
            "unlogged_error": bool(row["unlogged_error"]),
            "truth_final_z": row["truth_rollout"]["states"][-1],
            "truth_cost": float(row["truth_rollout"]["cost"]),
        }
        for row in per_start[:5]
    ]
    return {
        "seed": int(context["seed"]),
        "seed_index": int(context["seed_index"]),
        "arm": arm,
        "arm_label": ARM_LABELS[arm],
        "lambda_gap": float(lambda_gap),
        "config": {
            "sample_count": SAMPLE_COUNT,
            "rho": RHO,
            "use_torch": USE_TORCH,
            "train_fraction": TRAIN_FRACTION,
            "train_count": int(len(context["train_idx"])),
            "eval_count": int(len(context["eval_idx"])),
            "eval_start_count": int(len(context["starts"])),
            "planner_horizon": PLANNER_HORIZON,
            "action_count": len(ACTION_SET),
            "enumerated_sequence_count": len(ACTION_SET) ** PLANNER_HORIZON,
            "distinctions": list(DISTINCTIONS),
            "high_energy_threshold": float(context["high_energy_threshold"]),
            "gap_threshold": GAP_THRESHOLD,
            "error_threshold": ERROR_THRESHOLD,
        },
        "train_eval_split": {
            "train_count": int(len(context["train_idx"])),
            "eval_count": int(len(context["eval_idx"])),
            "start_count": int(len(context["starts"])),
            "train_index_checksum": int(np.sum(context["train_idx"])),
            "eval_index_checksum": int(np.sum(context["eval_idx"])),
            "start_indices": [int(index) for index in context["starts"]],
            "overlap_count": int(len(set(context["train_idx"].tolist()) & set(context["eval_idx"].tolist()))),
        },
        "dynamics_loss": {
            "latent_prediction_mse": float(model.train_latent_mse),
        },
        "metrics": {
            "distinction_stability": float(np.mean(np.all(_state_distinctions(context["z"][context["starts"]], high_energy_threshold=float(context["high_energy_threshold"])) == _state_distinctions(_true_next_z(context["z"][context["starts"]], np.zeros((len(context["starts"]), 2), dtype=np.float64)), high_energy_threshold=float(context["high_energy_threshold"])), axis=1))),
            "gap_auroc": _calibration_auc(gap_events, gap_scores),
            "gap_ece": _calibration_ece(gap_events, gap_scores),
            "UnloggedErrorRate": float(np.mean(unlogged_values)),
            "unsafe_state_rate": float(np.mean(unsafe_values)),
            "collision_rate": float(np.mean(collision_values)),
            "safe_planning_success": float(np.mean(success_values)),
            "planning_regret": float(np.mean(regret_values)),
            "prediction_error": float(np.mean(prediction_errors)),
            "predicted_gap_mean": float(np.mean(gap_scores)),
        },
        "start_state_audit_sample": audit_rows,
        "canonical_envelope_projection": context["canonical_envelope_projection"],
    }


def _records() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for index, seed in enumerate(_seeds(count=SEED_COUNT)):
        context = _seed_context(seed, index)
        models = _fit_arm_models(context)
        records.extend(_evaluate_seed(context, models))
    return records


def _stats_for(records: list[dict[str, Any]], metric: str) -> dict[str, float | int]:
    return metric_stats(float(record["metrics"][metric]) for record in records)


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_arm: dict[str, Any] = {}
    by_arm_lambda: dict[str, Any] = {}
    metrics = (
        "distinction_stability",
        "gap_auroc",
        "gap_ece",
        "UnloggedErrorRate",
        "unsafe_state_rate",
        "collision_rate",
        "safe_planning_success",
        "planning_regret",
        "prediction_error",
        "predicted_gap_mean",
    )
    for arm in ARM_ORDER:
        arm_records = [record for record in records if record["arm"] == arm]
        primary_records = [record for record in arm_records if float(record["lambda_gap"]) == PRIMARY_LAMBDA]
        by_arm[arm] = {
            "label": ARM_LABELS[arm],
            "record_count": len(arm_records),
            "primary_lambda": PRIMARY_LAMBDA,
            "primary_record_count": len(primary_records),
            "metrics": {metric: _stats_for(primary_records, metric) for metric in metrics},
        }
        by_arm_lambda[arm] = {}
        for lambda_gap in LAMBDA_GRID:
            lambda_records = [record for record in arm_records if float(record["lambda_gap"]) == float(lambda_gap)]
            by_arm_lambda[arm][str(lambda_gap)] = {
                "record_count": len(lambda_records),
                "metrics": {metric: _stats_for(lambda_records, metric) for metric in metrics},
            }
    return {
        "record_count": len(records),
        "seed_count": len({int(record["seed"]) for record in records}),
        "arm_count": len(ARM_ORDER),
        "lambda_count": len(LAMBDA_GRID),
        "records_per_seed": len(ARM_ORDER) * len(LAMBDA_GRID),
        "by_arm": by_arm,
        "by_arm_lambda": by_arm_lambda,
    }


def _paired_comparison(records: list[dict[str, Any]], metric: str) -> dict[str, Any]:
    model3 = {
        int(record["seed"]): float(record["metrics"][metric])
        for record in records
        if record["arm"] == "jepa_posthoc_bedc_report" and float(record["lambda_gap"]) == PRIMARY_LAMBDA
    }
    model4 = {
        int(record["seed"]): float(record["metrics"][metric])
        for record in records
        if record["arm"] == "bedc_jepa_end_to_end" and float(record["lambda_gap"]) == PRIMARY_LAMBDA
    }
    seeds = sorted(set(model3) & set(model4))
    diffs = [model4[seed] - model3[seed] for seed in seeds]
    n = len(diffs)
    mean_diff = float(np.mean(diffs)) if diffs else math.nan
    std = float(np.std(diffs, ddof=1)) if n > 1 else 0.0
    se = std / math.sqrt(n) if n > 1 else math.nan
    z_value = mean_diff / se if se and math.isfinite(se) and se > 0.0 else math.nan
    p_value = math.erfc(abs(z_value) / math.sqrt(2.0)) if math.isfinite(z_value) else math.nan
    favorable_direction = -1.0 if metric in {"unsafe_state_rate", "UnloggedErrorRate", "planning_regret", "collision_rate"} else 1.0
    return {
        "metric": metric,
        "primary_lambda": PRIMARY_LAMBDA,
        "paired_seed_count": n,
        "model3_mean": float(np.mean([model3[seed] for seed in seeds])) if seeds else math.nan,
        "model4_mean": float(np.mean([model4[seed] for seed in seeds])) if seeds else math.nan,
        "mean_difference_model4_minus_model3": mean_diff,
        "paired_std": std,
        "z_value": float(z_value) if math.isfinite(z_value) else math.nan,
        "approx_p_value": float(p_value) if math.isfinite(p_value) else math.nan,
        "model4_better": bool(math.isfinite(mean_diff) and favorable_direction * mean_diff > 0.0),
        "significant_at_0_05": bool(math.isfinite(p_value) and p_value < 0.05),
    }


def _model4_vs_model3(records: list[dict[str, Any]]) -> dict[str, Any]:
    metrics = (
        "unsafe_state_rate",
        "UnloggedErrorRate",
        "safe_planning_success",
        "planning_regret",
    )
    comparisons = {metric: _paired_comparison(records, metric) for metric in metrics}
    decisive = all(
        comparisons[metric]["model4_better"] and comparisons[metric]["significant_at_0_05"]
        for metric in ("unsafe_state_rate", "UnloggedErrorRate", "safe_planning_success")
    )
    return {
        "primary_lambda": PRIMARY_LAMBDA,
        "comparisons": comparisons,
        "headline_claim_supported": bool(decisive),
        "interpretation": (
            "The primary falsification check requires model 4 to beat model 3 on unsafe-state rate, "
            "UnloggedErrorRate, and safe-planning success at the primary lambda."
        ),
    }


def _planning_frontier(records: list[dict[str, Any]]) -> dict[str, Any]:
    frontier: dict[str, Any] = {}
    for arm in ARM_ORDER:
        frontier[arm] = []
        for lambda_gap in LAMBDA_GRID:
            rows = [
                record
                for record in records
                if record["arm"] == arm and float(record["lambda_gap"]) == float(lambda_gap)
            ]
            frontier[arm].append(
                {
                    "lambda_gap": float(lambda_gap),
                    "unsafe_state_rate": _stats_for(rows, "unsafe_state_rate"),
                    "UnloggedErrorRate": _stats_for(rows, "UnloggedErrorRate"),
                    "safe_planning_success": _stats_for(rows, "safe_planning_success"),
                    "planning_regret": _stats_for(rows, "planning_regret"),
                }
            )
    return frontier


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_gaussian_ou_dynamics_planning.py",
        "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
        "distinction_runner": "scripts/run_gaussian_ou_distinction_head.py",
        "toy_world": "bedc_quality_lab.toy_world.make_toy_batch",
        "stats_helper": "scripts/experiment_stats.py",
        "json_artifact": JSON_ARTIFACT,
        "report_artifact": REPORT_ARTIFACT,
        "import_dependency_chain": [
            "scripts/run_gaussian_ou_dynamics_planning.py",
            "scripts.run_gaussian_ou_lejepa.run_experiment",
            "scripts.run_gaussian_ou_distinction_head._seeds",
            "scripts.run_gaussian_ou_distinction_head._train_eval_split",
            "scripts.run_gaussian_ou_distinction_head._label_truth",
            "bedc_quality_lab.toy_world.make_toy_batch",
            "scripts.experiment_stats.metric_stats",
        ],
    }


def _applicability_boundary() -> dict[str, Any]:
    return {
        "admitted_family": "Gaussian-OU toy world with script-local action-conditioned replay.",
        "model": "Runner-local NumPy ridge dynamics predictor over z, distinction, gap, and action features.",
        "sample_count": SAMPLE_COUNT,
        "seed_count": SEED_COUNT,
        "arm_definitions": {arm: ARM_LABELS[arm] for arm in ARM_ORDER},
        "planner_horizon": PLANNER_HORIZON,
        "lambda_range": list(LAMBDA_GRID),
        "deterministic_fallback_boundary": (
            "The experiment uses the deterministic fallback latent surface from the existing Gaussian-OU lab "
            "runner and does not claim torch-only representation coverage."
        ),
        "hazard_boundary": {
            "hazard_center": HAZARD_CENTER.tolist(),
            "hazard_radius": HAZARD_RADIUS,
            "collision_radius": COLLISION_RADIUS,
            "world_bound": WORLD_BOUND,
        },
    }


def _negative_result_note() -> str:
    return (
        "The four-arm comparison is falsifiable: if the end-to-end arm does not beat the post-hoc BEDC "
        "report arm on the primary safety metrics, the report records that outcome directly."
    )


def _payload(records: list[dict[str, Any]]) -> dict[str, Any]:
    aggregate = _aggregate(records)
    return {
        "artifact_id": "bedc-quality-lab:gaussian-ou-dynamics-planning",
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "sample_count": SAMPLE_COUNT,
            "seed_count": SEED_COUNT,
            "seeds": _seeds(count=SEED_COUNT),
            "rho": RHO,
            "use_torch": USE_TORCH,
            "train_fraction": TRAIN_FRACTION,
            "planner_horizon": PLANNER_HORIZON,
            "eval_start_count": EVAL_START_COUNT,
            "lambda_values": list(LAMBDA_GRID),
            "primary_lambda": PRIMARY_LAMBDA,
            "action_set": [list(action) for action in ACTION_SET],
            "arms": list(ARM_ORDER),
            "expected_minimum_records": len(ARM_ORDER) * 20,
            "expected_record_count": SEED_COUNT * len(ARM_ORDER) * len(LAMBDA_GRID),
            "gap_threshold": GAP_THRESHOLD,
            "error_threshold": ERROR_THRESHOLD,
        },
        "source_artifacts": _source_artifacts(),
        "applicability_boundary": _applicability_boundary(),
        "negative_result_note": _negative_result_note(),
        "arms": {arm: {"label": ARM_LABELS[arm], **ARM_CONFIGS[arm].__dict__} for arm in ARM_ORDER},
        "lambda_values": list(LAMBDA_GRID),
        "records": records,
        "aggregate": aggregate,
        "model4_vs_model3": _model4_vs_model3(records),
        "planning_frontier": _planning_frontier(records),
        "safety_metrics": {
            arm: aggregate["by_arm"][arm]["metrics"]
            for arm in ARM_ORDER
        },
        "black_box_debt": {
            "unlogged_error_threshold": ERROR_THRESHOLD,
            "gap_reporting_threshold": GAP_THRESHOLD,
            "debt_vector": [
                "latent-only planning hides transition errors",
                "post-hoc reports can understate action-conditioned gap propagation",
                "end-to-end gap prediction is only validated on this finite toy family",
            ],
        },
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _render_stats(stats: dict[str, Any]) -> str:
    return (
        f"{_format_float(float(stats['mean']))} +/- {_format_float(float(stats['std']))} "
        f"(95% CI +/- {_format_float(float(stats['ci95_half_width']))})"
    )


def _render_report(payload: dict[str, Any]) -> str:
    aggregate = payload["aggregate"]
    lines = [
        "# Gaussian-OU Dynamics and Gap-Aware Planning",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Total records: `{aggregate['record_count']}`",
        f"- Seed count: `{aggregate['seed_count']}`",
        f"- Arm count: `{aggregate['arm_count']}`",
        f"- Lambda values: `{', '.join(str(value) for value in payload['lambda_values'])}`",
        f"- Primary lambda: `{payload['model4_vs_model3']['primary_lambda']}`",
        f"- Planner horizon: `{payload['config']['planner_horizon']}`",
        "",
        "## Four-Arm Primary Metrics",
        "",
        (
            "| arm | records | unsafe-state rate | UnloggedErrorRate | collision rate | "
            "safe-planning success | planning regret | gap AUROC | gap ECE |"
        ),
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for arm in ARM_ORDER:
        row = aggregate["by_arm"][arm]
        metrics = row["metrics"]
        lines.append(
            "| "
            f"{row['label']} | "
            f"{row['primary_record_count']} | "
            f"{_render_stats(metrics['unsafe_state_rate'])} | "
            f"{_render_stats(metrics['UnloggedErrorRate'])} | "
            f"{_render_stats(metrics['collision_rate'])} | "
            f"{_render_stats(metrics['safe_planning_success'])} | "
            f"{_render_stats(metrics['planning_regret'])} | "
            f"{_render_stats(metrics['gap_auroc'])} | "
            f"{_render_stats(metrics['gap_ece'])} |"
        )

    lines.extend(
        [
            "",
            "## Model 4 vs Model 3",
            "",
            "| metric | model 3 mean | model 4 mean | model4 - model3 | z | approx p | model4 better | significant |",
            "| --- | ---: | ---: | ---: | ---: | ---: | --- | --- |",
        ]
    )
    for metric, comparison in payload["model4_vs_model3"]["comparisons"].items():
        lines.append(
            "| "
            f"{metric} | "
            f"{_format_float(float(comparison['model3_mean']))} | "
            f"{_format_float(float(comparison['model4_mean']))} | "
            f"{_format_float(float(comparison['mean_difference_model4_minus_model3']))} | "
            f"{_format_float(float(comparison['z_value']))} | "
            f"{_format_float(float(comparison['approx_p_value']))} | "
            f"{comparison['model4_better']} | "
            f"{comparison['significant_at_0_05']} |"
        )
    lines.append("")
    lines.append(f"Headline claim supported: `{payload['model4_vs_model3']['headline_claim_supported']}`")

    lines.extend(
        [
            "",
            "## Lambda Safety/Cost Frontier",
            "",
            "| arm | lambda | unsafe-state rate | UnloggedErrorRate | safe-planning success | planning regret |",
            "| --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for arm in ARM_ORDER:
        for row in payload["planning_frontier"][arm]:
            lines.append(
                "| "
                f"{ARM_LABELS[arm]} | "
                f"{row['lambda_gap']} | "
                f"{_render_stats(row['unsafe_state_rate'])} | "
                f"{_render_stats(row['UnloggedErrorRate'])} | "
                f"{_render_stats(row['safe_planning_success'])} | "
                f"{_render_stats(row['planning_regret'])} |"
            )

    lines.extend(["", "## Applicability Boundary", ""])
    for key, value in payload["applicability_boundary"].items():
        lines.append(f"- {key}: `{json.dumps(value, sort_keys=True)}`")

    lines.extend(
        [
            "",
            "## Negative Result Note",
            "",
            payload["negative_result_note"],
            "",
            "## Source Artifacts",
            "",
            f"- Generation script: `{payload['source_artifacts']['generation_script']}`",
            f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
            f"- Distinction runner: `{payload['source_artifacts']['distinction_runner']}`",
            f"- JSON artifact: `{payload['source_artifacts']['json_artifact']}`",
            f"- Report artifact: `{payload['source_artifacts']['report_artifact']}`",
            "- Import dependency chain:",
        ]
    )
    for item in payload["source_artifacts"]["import_dependency_chain"]:
        lines.append(f"  - `{item}`")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def main() -> None:
    payload = _payload(_records())
    expected_floor = len(ARM_ORDER) * 20
    if len(payload["records"]) < expected_floor:
        raise RuntimeError(f"record floor not met: {len(payload['records'])} < {expected_floor}")
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"records {len(payload['records'])}")


if __name__ == "__main__":
    main()
