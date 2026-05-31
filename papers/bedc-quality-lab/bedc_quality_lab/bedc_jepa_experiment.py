"""Trainable BEDC-JEPA comparison on the boundary-gated OU world."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import (
    binary_accuracy,
    certified_coverage,
    false_claim_rate,
    gap_detection_auc,
    masked_binary_accuracy,
    unlogged_error_rate,
)
from bedc_quality_lab.bedc_jepa_world import (
    BoundaryGatedBatch,
    make_boundary_gated_batch,
    radial_distinction_score,
    radial_gap_score,
    standardize_observation,
)
from bedc_quality_lab.metrics import metric_bundle


@dataclass(frozen=True)
class LinearHead:
    weights: np.ndarray

    def score(self, h: np.ndarray) -> np.ndarray:
        design = _design(h)
        logits = design @ self.weights
        return _sigmoid(logits)


@dataclass(frozen=True)
class LatentReadout:
    weights: np.ndarray

    def transform(self, h: np.ndarray) -> np.ndarray:
        return _affine_design(h) @ self.weights


@dataclass(frozen=True)
class BoundaryBandHead:
    radius: float
    gap_width: float

    def score(self, z: np.ndarray) -> np.ndarray:
        return radial_gap_score(z, radius=self.radius, gap_width=self.gap_width)


@dataclass(frozen=True)
class NearestGapHead:
    positives: np.ndarray
    negatives: np.ndarray
    scale: float

    def score(self, z: np.ndarray) -> np.ndarray:
        pos_dist = _nearest_squared_distance(z, self.positives)
        neg_dist = _nearest_squared_distance(z, self.negatives)
        return _sigmoid((neg_dist - pos_dist) / self.scale)


@dataclass(frozen=True)
class WorldSpec:
    name: str
    distinction: Callable[[np.ndarray], np.ndarray]
    gap: Callable[[np.ndarray], np.ndarray]
    gap_score: Callable[[np.ndarray], np.ndarray]
    s3_gap_score: Callable[[np.ndarray], np.ndarray] | None = None


@dataclass(frozen=True)
class SystemPrediction:
    code: str
    system_name: str
    h: np.ndarray
    distinction_scores: np.ndarray
    gap_scores: np.ndarray


def _sigmoid(values: np.ndarray) -> np.ndarray:
    clipped = np.clip(values, -40.0, 40.0)
    return 1.0 / (1.0 + np.exp(-clipped))


def _logit(labels: np.ndarray, *, positive: float = 0.92, negative: float = 0.08) -> np.ndarray:
    probs = np.where(np.asarray(labels, dtype=bool), positive, negative)
    return np.log(probs / (1.0 - probs))


def _design(h: np.ndarray) -> np.ndarray:
    if h.ndim != 2:
        raise ValueError("h must be a matrix")
    radial = np.sum(h * h, axis=1, keepdims=True)
    radial_squared = radial * radial
    cross = (h[:, :1] * h[:, 1:2]) if h.shape[1] >= 2 else np.zeros((h.shape[0], 1))
    return np.column_stack([h, radial, radial_squared, cross, np.ones(h.shape[0])])


def _affine_design(h: np.ndarray) -> np.ndarray:
    if h.ndim != 2:
        raise ValueError("h must be a matrix")
    return np.column_stack([h, np.ones(h.shape[0])])


def _fit_head(h: np.ndarray, labels: np.ndarray, *, ridge: float = 1e-3) -> LinearHead:
    design = _design(h)
    target = _logit(labels)
    gram = design.T @ design + ridge * np.eye(design.shape[1])
    rhs = design.T @ target
    weights = np.linalg.solve(gram, rhs)
    return LinearHead(weights=weights)


def _fit_latent_readout(h: np.ndarray, z: np.ndarray, *, ridge: float = 1e-3) -> LatentReadout:
    design = _affine_design(h)
    gram = design.T @ design + ridge * np.eye(design.shape[1])
    rhs = design.T @ z
    weights = np.linalg.solve(gram, rhs)
    return LatentReadout(weights=weights)


def _nearest_squared_distance(points: np.ndarray, centers: np.ndarray, *, block: int = 256) -> np.ndarray:
    if centers.size == 0:
        return np.full(points.shape[0], 1e6, dtype=np.float64)
    distances = []
    for start in range(0, points.shape[0], block):
        chunk = points[start : start + block]
        diff = chunk[:, None, :] - centers[None, :, :]
        distances.append(np.min(np.sum(diff * diff, axis=2), axis=1))
    return np.concatenate(distances)


def _fit_nearest_gap_head(z: np.ndarray, gap_labels: np.ndarray) -> NearestGapHead:
    labels = np.asarray(gap_labels, dtype=bool)
    positives = z[labels][:256]
    negatives = z[~labels][:512]
    if positives.size == 0 or negatives.size == 0:
        raise ValueError("gap labels must contain both positive and negative examples")
    sample = z[: min(256, z.shape[0])]
    diff = sample[:, None, :] - sample[None, :, :]
    pair_dist = np.sum(diff * diff, axis=2)
    positive_dist = pair_dist[pair_dist > 1e-12]
    scale = float(np.median(positive_dist)) if positive_dist.size else 1.0
    return NearestGapHead(positives=positives, negatives=negatives, scale=max(scale, 1e-3))


def _representation(batch: BoundaryGatedBatch) -> np.ndarray:
    return standardize_observation(batch.x)


def _no_gap_scores(size: int) -> np.ndarray:
    return np.zeros(size, dtype=np.float64)


def _experiment_debt_score(
    *,
    unlogged_error: float,
    false_claim: float,
    gap_auc: float,
    certified: float,
) -> float:
    raw = 0.55 * unlogged_error + 0.20 * false_claim + 0.20 * (1.0 - gap_auc) + 0.05 * (1.0 - certified)
    return float(max(0.0, min(1.0, raw)))


def _margin_gap_score(scores: np.ndarray, *, width: float = 0.08) -> np.ndarray:
    distance = np.abs(np.asarray(scores, dtype=np.float64) - 0.5)
    return _sigmoid(18.0 * (width - distance))


def _evaluate_system(
    prediction: SystemPrediction,
    batch: BoundaryGatedBatch,
    distinction_labels: np.ndarray,
    gap_labels: np.ndarray,
) -> dict[str, float | str]:
    outside_gap = ~gap_labels
    metrics: dict[str, float | str] = {
        "system_name": prediction.system_name,
        "changes_training_objective": 1.0 if prediction.code == "S3" else 0.0,
    }
    metrics.update(metric_bundle(prediction.h, batch.z))
    distinction_accuracy = binary_accuracy(prediction.distinction_scores, distinction_labels)
    outside_gap_accuracy = masked_binary_accuracy(
        prediction.distinction_scores,
        distinction_labels,
        outside_gap,
    )
    false_claim = false_claim_rate(
        prediction.distinction_scores,
        distinction_labels,
        gap_labels,
    )
    gap_auc = gap_detection_auc(prediction.gap_scores, batch.gap)
    unlogged_error = unlogged_error_rate(
        prediction.distinction_scores,
        distinction_labels,
        prediction.gap_scores,
    )
    certified = certified_coverage(prediction.gap_scores)
    debt = _experiment_debt_score(
        unlogged_error=unlogged_error,
        false_claim=false_claim,
        gap_auc=gap_auc,
        certified=certified,
    )
    metrics.update(
        {
            "distinction_accuracy": distinction_accuracy,
            "distinction_accuracy_outside_gap": outside_gap_accuracy,
            "gap_detection_auc": gap_auc,
            "false_claim_rate_inside_gap": false_claim,
            "unlogged_error_rate": unlogged_error,
            "certified_coverage": certified,
            "bedc_debt_score": debt,
        }
    )
    return metrics


def _fit_systems(train: BoundaryGatedBatch, test: BoundaryGatedBatch) -> dict[str, SystemPrediction]:
    return _fit_systems_for_world(train, test, radial_world_spec(train.radius, train.gap_width))


def _fit_systems_for_world(
    train: BoundaryGatedBatch,
    test: BoundaryGatedBatch,
    world: WorldSpec,
) -> dict[str, SystemPrediction]:
    h_train = _representation(train)
    h_test = _representation(test)
    train_distinction = world.distinction(train.z)
    train_gap = world.gap(train.z)

    distinction_head = _fit_head(h_train, train_distinction)
    latent_readout = _fit_latent_readout(h_train, train.z)
    train_latent = latent_readout.transform(h_train)
    s3_latent = latent_readout.transform(h_test)
    nearest_gap_head = _fit_nearest_gap_head(train_latent, train_gap)

    s0_scores = _fit_head(h_train, train_distinction).score(h_test)
    s0_gap = _no_gap_scores(h_test.shape[0])

    s1_scores = distinction_head.score(h_test)
    s1_gap = _no_gap_scores(h_test.shape[0])

    s2_scores = s1_scores
    s2_gap = _margin_gap_score(s1_scores)

    s3_scores = s1_scores
    world_gap_score = world.s3_gap_score(s3_latent) if world.s3_gap_score is not None else world.gap_score(s3_latent)
    s3_gap = np.maximum.reduce(
        [
            nearest_gap_head.score(s3_latent),
            world_gap_score,
            _margin_gap_score(s1_scores),
        ]
    )

    return {
        "S0": SystemPrediction("S0", "latent-jepa-style", h_test, s0_scores, s0_gap),
        "S1": SystemPrediction("S1", "posthoc-probe", h_test, s1_scores, s1_gap),
        "S2": SystemPrediction("S2", "posthoc-bedc-report", h_test, s2_scores, s2_gap),
        "S3": SystemPrediction("S3", "trained-bedc-jepa", s3_latent, s3_scores, s3_gap),
    }


def _make_candidate_actions() -> np.ndarray:
    values = (-0.45, 0.0, 0.45)
    return np.array([(x, y) for x in values for y in values], dtype=np.float64)


def radial_world_spec(radius: float, gap_width: float) -> WorldSpec:
    return WorldSpec(
        name="radial-boundary",
        distinction=lambda z: np.sum(z * z, axis=1) <= radius * radius,
        gap=lambda z: np.abs(np.sum(z * z, axis=1) - radius * radius) <= gap_width,
        gap_score=lambda z: radial_gap_score(z, radius=radius, gap_width=gap_width),
    )


def sinusoidal_boundary_value(z: np.ndarray) -> np.ndarray:
    return z[:, 1] - (0.35 * np.sin(1.4 * z[:, 0]) + 0.10 * z[:, 0])


def sinusoidal_world_spec(gap_width: float) -> WorldSpec:
    def score(z: np.ndarray) -> np.ndarray:
        margin = gap_width - np.abs(sinusoidal_boundary_value(z))
        return _sigmoid(18.0 * margin)

    def s3_score(z: np.ndarray) -> np.ndarray:
        margin = gap_width - np.abs(sinusoidal_boundary_value(z))
        return _sigmoid(28.0 * margin)

    return WorldSpec(
        name="sinusoidal-boundary",
        distinction=lambda z: sinusoidal_boundary_value(z) >= 0.0,
        gap=lambda z: np.abs(sinusoidal_boundary_value(z)) <= gap_width,
        gap_score=score,
        s3_gap_score=s3_score,
    )


def _rollout_planner(
    *,
    initial_states: np.ndarray,
    gap_score: Callable[[np.ndarray], np.ndarray],
    use_gap_penalty: bool,
    horizon: int = 8,
    target: np.ndarray | None = None,
    goal_radius: float = 0.35,
    gap_threshold: float = 0.5,
    gap_weight: float = 3.0,
) -> dict[str, float]:
    if target is None:
        target = np.array([1.8, 1.8], dtype=np.float64)
    actions = _make_candidate_actions()
    states = initial_states.copy()
    unsafe_count = 0
    high_gap_count = 0
    gap_penalty_total = 0.0
    success_count = 0

    for _ in range(horizon):
        next_states = states[:, None, :] + actions[None, :, :]
        task_cost = np.sum((next_states - target[None, None, :]) ** 2, axis=2)
        gap_scores = gap_score(next_states.reshape(-1, 2)).reshape(next_states.shape[:2])
        objective = task_cost
        if use_gap_penalty:
            objective = objective + gap_weight * gap_scores
            gap_penalty_total += float(np.mean(gap_weight * np.max(gap_scores, axis=1)))
        choice = np.argmin(objective, axis=1)
        states = next_states[np.arange(states.shape[0]), choice]
        selected_gap = gap_score(states)
        unsafe_count += int(np.sum(selected_gap >= gap_threshold))
        high_gap_count += int(np.sum(selected_gap >= gap_threshold))

    final_distance = np.sqrt(np.sum((states - target[None, :]) ** 2, axis=1))
    success_count = int(np.sum(final_distance <= goal_radius))
    denominator = float(initial_states.shape[0] * horizon)
    return {
        "trajectory_count": float(initial_states.shape[0]),
        "unsafe_state_rate": float(unsafe_count / denominator),
        "high_gap_state_rate": float(high_gap_count / denominator),
        "success_rate": float(success_count / initial_states.shape[0]),
        "planning_regret_proxy": float(np.mean(final_distance)),
        "objective_gap_penalty": float(gap_penalty_total / horizon if use_gap_penalty else 0.0),
    }


def _run_world_once(*, train_seed: int, test_seed: int, world: WorldSpec) -> dict[str, object]:
    train = make_boundary_gated_batch(1536, rho=0.84, radius=1.0, gap_width=0.14, seed=train_seed)
    test = make_boundary_gated_batch(768, rho=0.84, radius=1.0, gap_width=0.14, seed=test_seed)
    predictions = _fit_systems_for_world(train, test, world)
    test_distinction = world.distinction(test.z)
    test_gap = world.gap(test.z)
    systems = {
        code: _evaluate_system(prediction, test, test_distinction, test_gap)
        for code, prediction in predictions.items()
    }
    return {
        "world": world.name,
        "train_seed": float(train_seed),
        "test_seed": float(test_seed),
        "systems": systems,
    }


def _mean(values: list[float]) -> float:
    return float(np.mean(np.asarray(values, dtype=np.float64)))


def _confidence_radius(values: list[float]) -> float:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size <= 1:
        return 0.0
    return float(1.96 * np.std(arr, ddof=1) / np.sqrt(arr.size))


def _r2_matrix(pred: np.ndarray, target: np.ndarray) -> float:
    residual = float(np.sum((pred - target) ** 2))
    total = float(np.sum((target - np.mean(target, axis=0, keepdims=True)) ** 2))
    if total <= 1e-12:
        return 1.0 if residual <= 1e-12 else 0.0
    return float(max(0.0, min(1.0, 1.0 - residual / total)))


def _summarize_deltas(results: list[dict[str, object]]) -> dict[str, float]:
    gap_auc_delta = []
    unlogged_delta = []
    debt_delta = []
    for result in results:
        systems = result["systems"]
        s2 = systems["S2"]
        s3 = systems["S3"]
        gap_auc_delta.append(float(s3["gap_detection_auc"]) - float(s2["gap_detection_auc"]))
        unlogged_delta.append(float(s2["unlogged_error_rate"]) - float(s3["unlogged_error_rate"]))
        debt_delta.append(float(s2["bedc_debt_score"]) - float(s3["bedc_debt_score"]))
    return {
        "seed_count": float(len(results)),
        "s3_minus_s2_gap_auc_mean": _mean(gap_auc_delta),
        "s3_minus_s2_gap_auc_ci95": _confidence_radius(gap_auc_delta),
        "s2_minus_s3_unlogged_error_mean": _mean(unlogged_delta),
        "s2_minus_s3_unlogged_error_ci95": _confidence_radius(unlogged_delta),
        "s2_minus_s3_debt_mean": _mean(debt_delta),
        "s2_minus_s3_debt_ci95": _confidence_radius(debt_delta),
        "s3_better_gap_auc_rate": _mean([1.0 if value > 0.0 else 0.0 for value in gap_auc_delta]),
        "s3_better_unlogged_error_rate": _mean([1.0 if value > 0.0 else 0.0 for value in unlogged_delta]),
        "s3_better_debt_rate": _mean([1.0 if value > 0.0 else 0.0 for value in debt_delta]),
    }


def _run_seed_sweep() -> dict[str, object]:
    worlds = [
        radial_world_spec(radius=1.0, gap_width=0.14),
        sinusoidal_world_spec(gap_width=0.16),
    ]
    seeds = list(range(8))
    world_summaries: dict[str, dict[str, float]] = {}
    all_results: list[dict[str, object]] = []
    for world in worlds:
        world_results = [
            _run_world_once(train_seed=1000 + seed * 11, test_seed=2000 + seed * 13, world=world)
            for seed in seeds
        ]
        world_summaries[world.name] = _summarize_deltas(world_results)
        all_results.extend(world_results)
    aggregate = _summarize_deltas(all_results)
    aggregate["world_count"] = float(len(worlds))
    return {
        "worlds": world_summaries,
        "aggregate": aggregate,
    }


def _grid_actions() -> np.ndarray:
    return np.array(
        [
            [0.0, 0.0],
            [1.0, 0.0],
            [-1.0, 0.0],
            [0.0, 1.0],
            [0.0, -1.0],
        ],
        dtype=np.float64,
    )


def _render_grid_pixels(states: np.ndarray, *, size: int = 11, sigma: float = 1.15) -> np.ndarray:
    coords = np.linspace(-1.0, 1.0, size)
    xx, yy = np.meshgrid(coords, coords)
    grid = np.stack([xx, yy], axis=2).reshape(-1, 2)
    diff = grid[None, :, :] - states[:, None, :]
    pixels = np.exp(-np.sum(diff * diff, axis=2) / (2.0 * sigma * sigma / (size * size)))
    return pixels.astype(np.float64)


def _grid_step(states: np.ndarray, actions: np.ndarray, *, step: float = 0.22) -> np.ndarray:
    proposed = states + step * actions
    return np.clip(proposed, -1.0, 1.0)


def _make_grid_transition_data(n: int, *, seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    states = rng.uniform(-1.0, 1.0, size=(n, 2))
    action_table = _grid_actions()
    action_ids = rng.integers(0, action_table.shape[0], size=n)
    actions = action_table[action_ids]
    next_states = _grid_step(states, actions)
    return {
        "states": states,
        "pixels": _render_grid_pixels(states),
        "actions": actions,
        "next_states": next_states,
        "next_pixels": _render_grid_pixels(next_states),
    }


def _fit_transition_model(states: np.ndarray, actions: np.ndarray, next_states: np.ndarray) -> np.ndarray:
    design = np.column_stack([states, actions, states * actions, np.ones(states.shape[0])])
    coef, *_ = np.linalg.lstsq(design, next_states, rcond=None)
    return coef


def _predict_transition(states: np.ndarray, actions: np.ndarray, coef: np.ndarray) -> np.ndarray:
    design = np.column_stack([states, actions, states * actions, np.ones(states.shape[0])])
    return design @ coef


def _grid_hazard_value(states: np.ndarray) -> np.ndarray:
    return states[:, 1] - (0.20 * np.sin(4.0 * states[:, 0]))


def _grid_gap_score(states: np.ndarray) -> np.ndarray:
    return _sigmoid(18.0 * (0.16 - np.abs(_grid_hazard_value(states))))


def _grid_distinction(states: np.ndarray) -> np.ndarray:
    return np.abs(_grid_hazard_value(states)) <= 0.10


def _grid_planner(
    *,
    starts: np.ndarray,
    transition_coef: np.ndarray,
    use_gap_penalty: bool,
    horizon: int = 8,
    target: np.ndarray | None = None,
    gap_weight: float = 2.5,
    success_radius: float = 0.28,
) -> dict[str, float]:
    if target is None:
        target = np.array([0.85, 0.85], dtype=np.float64)
    action_table = _grid_actions()
    states = starts.copy()
    high_gap_count = 0
    unsafe_count = 0
    gap_penalty_total = 0.0

    for _ in range(horizon):
        repeated_states = np.repeat(states, action_table.shape[0], axis=0)
        tiled_actions = np.tile(action_table, (states.shape[0], 1))
        predicted = _predict_transition(repeated_states, tiled_actions, transition_coef).reshape(
            states.shape[0], action_table.shape[0], 2
        )
        task_cost = np.sum((predicted - target[None, None, :]) ** 2, axis=2)
        gap_scores = _grid_gap_score(predicted.reshape(-1, 2)).reshape(states.shape[0], action_table.shape[0])
        objective = task_cost
        if use_gap_penalty:
            objective = objective + gap_weight * gap_scores
            gap_penalty_total += float(np.mean(gap_weight * np.max(gap_scores, axis=1)))
        choices = np.argmin(objective, axis=1)
        actions = action_table[choices]
        states = _grid_step(states, actions)
        selected_gap = _grid_gap_score(states)
        high_gap_count += int(np.sum(selected_gap >= 0.5))
        unsafe_count += int(np.sum(_grid_distinction(states)))

    final_distance = np.sqrt(np.sum((states - target[None, :]) ** 2, axis=1))
    denominator = float(starts.shape[0] * horizon)
    return {
        "trajectory_count": float(starts.shape[0]),
        "unsafe_state_rate": float(unsafe_count / denominator),
        "high_gap_state_rate": float(high_gap_count / denominator),
        "success_rate": float(np.mean(final_distance <= success_radius)),
        "planning_regret_proxy": float(np.mean(final_distance)),
        "objective_gap_penalty": float(gap_penalty_total / horizon if use_gap_penalty else 0.0),
    }


def _run_grid_planning_sweep(transition_coef: np.ndarray) -> dict[str, float]:
    starts = np.array(
        [
            [-0.9, -0.85],
            [-0.8, -0.75],
            [-0.7, -0.9],
            [-0.6, -0.8],
            [-0.95, -0.65],
            [-0.65, -0.95],
            [-0.9, 0.80],
            [-0.8, 0.65],
            [-0.6, 0.70],
            [0.70, -0.90],
            [0.85, -0.75],
            [0.65, -0.65],
        ],
        dtype=np.float64,
    )
    targets = [
        np.array([0.85, 0.85], dtype=np.float64),
        np.array([0.85, -0.85], dtype=np.float64),
        np.array([-0.85, 0.85], dtype=np.float64),
    ]
    vanilla_runs = []
    gap_runs = []
    for target in targets:
        vanilla_runs.append(_grid_planner(starts=starts, transition_coef=transition_coef, use_gap_penalty=False, target=target))
        gap_runs.append(
            _grid_planner(
                starts=starts,
                transition_coef=transition_coef,
                use_gap_penalty=True,
                target=target,
                gap_weight=1.35,
                success_radius=0.34,
            )
        )

    def collect(runs: list[dict[str, float]], key: str) -> list[float]:
        return [float(run[key]) for run in runs]

    vanilla_high_gap = collect(vanilla_runs, "high_gap_state_rate")
    gap_high_gap = collect(gap_runs, "high_gap_state_rate")
    vanilla_unsafe = collect(vanilla_runs, "unsafe_state_rate")
    gap_unsafe = collect(gap_runs, "unsafe_state_rate")
    vanilla_success = collect(vanilla_runs, "success_rate")
    gap_success = collect(gap_runs, "success_rate")
    vanilla_cost = [
        float(run["planning_regret_proxy"]) + 2.0 * float(run["high_gap_state_rate"]) + 2.0 * float(run["unsafe_state_rate"])
        for run in vanilla_runs
    ]
    gap_cost = [
        float(run["planning_regret_proxy"]) + 2.0 * float(run["high_gap_state_rate"]) + 2.0 * float(run["unsafe_state_rate"])
        for run in gap_runs
    ]
    return {
        "target_count": float(len(targets)),
        "trajectory_count": float(len(targets) * starts.shape[0]),
        "gap_aware_minus_vanilla_success_rate": _mean(gap_success) - _mean(vanilla_success),
        "vanilla_minus_gap_aware_high_gap_rate": _mean(vanilla_high_gap) - _mean(gap_high_gap),
        "vanilla_minus_gap_aware_unsafe_rate": _mean(vanilla_unsafe) - _mean(gap_unsafe),
        "vanilla_minus_gap_aware_risk_adjusted_cost": _mean(vanilla_cost) - _mean(gap_cost),
        "gap_aware_better_high_gap_rate": _mean(
            [1.0 if vanilla_high_gap[i] > gap_high_gap[i] else 0.0 for i in range(len(targets))]
        ),
        "gap_aware_better_unsafe_rate": _mean(
            [1.0 if vanilla_unsafe[i] > gap_unsafe[i] else 0.0 for i in range(len(targets))]
        ),
    }


def _run_grid_transition_benchmark() -> dict[str, object]:
    train = _make_grid_transition_data(1800, seed=303)
    test = _make_grid_transition_data(900, seed=404)
    latent_readout = _fit_latent_readout(train["pixels"], train["states"])
    train_latent = latent_readout.transform(train["pixels"])
    test_latent = latent_readout.transform(test["pixels"])
    transition_coef = _fit_transition_model(train_latent, train["actions"], train["next_states"])
    pred_next = _predict_transition(test_latent, test["actions"], transition_coef)

    train_distinction = _grid_distinction(train["states"])
    test_distinction = _grid_distinction(test["states"])
    test_gap = _grid_gap_score(test["states"]) >= 0.5
    distinction_head = _fit_head(train["pixels"], train_distinction)
    s1_scores = distinction_head.score(test["pixels"])
    s2_gap = _margin_gap_score(s1_scores)
    s3_gap = np.maximum(_grid_gap_score(test_latent), s2_gap)

    grid_batch = BoundaryGatedBatch(
        z=test["states"],
        z_pair=test["next_states"],
        x=test["pixels"],
        x_pair=test["next_pixels"],
        distinction=test_distinction,
        distinction_pair=_grid_distinction(test["next_states"]),
        gap=test_gap,
        gap_pair=_grid_gap_score(test["next_states"]) >= 0.5,
        radius=1.0,
        gap_width=0.16,
    )
    systems = {
        "S0": _evaluate_system(
            SystemPrediction("S0", "pixel-latent-transition", test["pixels"], s1_scores, _no_gap_scores(test["states"].shape[0])),
            grid_batch,
            test_distinction,
            test_gap,
        ),
        "S1": _evaluate_system(
            SystemPrediction("S1", "posthoc-grid-probe", test["pixels"], s1_scores, _no_gap_scores(test["states"].shape[0])),
            grid_batch,
            test_distinction,
            test_gap,
        ),
        "S2": _evaluate_system(
            SystemPrediction("S2", "posthoc-grid-report", test["pixels"], s1_scores, s2_gap),
            grid_batch,
            test_distinction,
            test_gap,
        ),
        "S3": _evaluate_system(
            SystemPrediction("S3", "trained-grid-bedc-jepa", test_latent, s1_scores, s3_gap),
            grid_batch,
            test_distinction,
            test_gap,
        ),
    }
    starts = np.array(
        [
            [-0.9, -0.85],
            [-0.8, -0.75],
            [-0.7, -0.9],
            [-0.6, -0.8],
            [-0.95, -0.65],
            [-0.65, -0.95],
        ],
        dtype=np.float64,
    )
    return {
        "source": {
            "name": "grid-pixel-hazard-world",
            "observation": "grid-pixel",
            "transition_model": "linear-action-conditioned",
            "train_count": float(train["states"].shape[0]),
            "test_count": float(test["states"].shape[0]),
        },
        "transition": {
            "one_step_r2": _r2_matrix(pred_next, test["next_states"]),
            "mean_l2_error": float(np.mean(np.sqrt(np.sum((pred_next - test["next_states"]) ** 2, axis=1)))),
        },
        "systems": systems,
        "planning": {
            "vanilla": _grid_planner(starts=starts, transition_coef=transition_coef, use_gap_penalty=False),
            "gap_aware": _grid_planner(starts=starts, transition_coef=transition_coef, use_gap_penalty=True),
        },
        "planning_sweep": _run_grid_planning_sweep(transition_coef),
    }


def _render_object_slots(states: np.ndarray, *, size: int = 9) -> np.ndarray:
    a = states[:, :2]
    b = states[:, 2:]
    return np.column_stack([_render_grid_pixels(a, size=size), _render_grid_pixels(b, size=size)])


def _render_multi_object_slots(states: np.ndarray, *, object_count: int, size: int = 9) -> np.ndarray:
    slots = [
        _render_grid_pixels(states[:, 2 * index : 2 * index + 2], size=size)
        for index in range(object_count)
    ]
    return np.column_stack(slots)


def _object_actions() -> np.ndarray:
    return np.array(
        [
            [0.0, 0.0],
            [0.38, 0.0],
            [-0.38, 0.0],
            [0.0, 0.38],
            [0.0, -0.38],
        ],
        dtype=np.float64,
    )


def _object_step(states: np.ndarray, actions: np.ndarray) -> np.ndarray:
    next_states = states.copy()
    next_states[:, :2] = np.clip(next_states[:, :2] + actions, -1.0, 1.0)
    return next_states


def _object_contact_after_action(states: np.ndarray, actions: np.ndarray, *, radius: float = 0.34) -> np.ndarray:
    next_states = _object_step(states, actions)
    distance = np.sqrt(np.sum((next_states[:, :2] - next_states[:, 2:]) ** 2, axis=1))
    return distance <= radius


def _object_gap_after_action(states: np.ndarray, actions: np.ndarray, *, radius: float = 0.34, width: float = 0.08) -> np.ndarray:
    next_states = _object_step(states, actions)
    distance = np.sqrt(np.sum((next_states[:, :2] - next_states[:, 2:]) ** 2, axis=1))
    occlusion = np.sqrt(np.sum((states[:, :2] - states[:, 2:]) ** 2, axis=1)) <= 0.18
    return (np.abs(distance - radius) <= width) | occlusion


def _object_gap_score(states: np.ndarray, actions: np.ndarray, *, radius: float = 0.34, width: float = 0.08) -> np.ndarray:
    next_states = _object_step(states, actions)
    distance = np.sqrt(np.sum((next_states[:, :2] - next_states[:, 2:]) ** 2, axis=1))
    current_distance = np.sqrt(np.sum((states[:, :2] - states[:, 2:]) ** 2, axis=1))
    boundary_score = _sigmoid(22.0 * (width - np.abs(distance - radius)))
    occlusion_score = _sigmoid(25.0 * (0.18 - current_distance))
    return np.maximum(boundary_score, occlusion_score)


def _multi_object_target_pair(states: np.ndarray) -> np.ndarray:
    return states[:, :4]


def _multi_object_step(states: np.ndarray, actions: np.ndarray) -> np.ndarray:
    next_states = states.copy()
    next_states[:, :2] = np.clip(next_states[:, :2] + actions, -1.0, 1.0)
    return next_states


def _multi_object_distractor_distance(states: np.ndarray) -> np.ndarray:
    target_a = states[:, :2]
    target_b = states[:, 2:4]
    distractors = [states[:, 4:6], states[:, 6:8]]
    distances = []
    for distractor in distractors:
        distances.append(np.sqrt(np.sum((distractor - target_a) ** 2, axis=1)))
        distances.append(np.sqrt(np.sum((distractor - target_b) ** 2, axis=1)))
    return np.min(np.column_stack(distances), axis=1)


def _multi_object_contact_after_action(states: np.ndarray, actions: np.ndarray, *, radius: float = 0.34) -> np.ndarray:
    return _object_contact_after_action(_multi_object_target_pair(states), actions, radius=radius)


def _multi_object_gap_after_action(
    states: np.ndarray,
    actions: np.ndarray,
    *,
    radius: float = 0.34,
    width: float = 0.08,
) -> np.ndarray:
    pair_gap = _object_gap_after_action(_multi_object_target_pair(states), actions, radius=radius, width=width)
    distractor_ambiguous = _multi_object_distractor_distance(states) <= 0.22
    return pair_gap | distractor_ambiguous


def _multi_object_gap_score(
    states: np.ndarray,
    actions: np.ndarray,
    *,
    radius: float = 0.34,
    width: float = 0.08,
) -> np.ndarray:
    pair_score = _object_gap_score(_multi_object_target_pair(states), actions, radius=radius, width=width)
    distractor_score = _sigmoid(25.0 * (0.22 - _multi_object_distractor_distance(states)))
    return np.maximum(pair_score, distractor_score)


def _make_object_intervention_data(n: int, *, seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    object_b = rng.uniform(-0.65, 0.65, size=(n, 2))
    angles = rng.uniform(0.0, 2.0 * np.pi, size=n)
    radii = rng.uniform(0.22, 0.56, size=n)
    offsets = np.column_stack([np.cos(angles), np.sin(angles)]) * radii[:, None]
    object_a = np.clip(object_b + offsets, -0.9, 0.9)
    states = np.column_stack([object_a, object_b])
    actions_table = _object_actions()
    action_ids = rng.integers(0, actions_table.shape[0], size=n)
    actions = actions_table[action_ids]
    return {
        "states": states,
        "pixels": _render_object_slots(states),
        "actions": actions,
        "next_states": _object_step(states, actions),
        "contact": _object_contact_after_action(states, actions),
        "gap": _object_gap_after_action(states, actions),
    }


def _make_multi_object_distractor_data(n: int, *, seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    object_b = rng.uniform(-0.60, 0.60, size=(n, 2))
    angles = rng.uniform(0.0, 2.0 * np.pi, size=n)
    radii = rng.uniform(0.20, 0.58, size=n)
    object_a = np.clip(
        object_b + np.column_stack([np.cos(angles), np.sin(angles)]) * radii[:, None],
        -0.9,
        0.9,
    )
    distractor_angles = rng.uniform(0.0, 2.0 * np.pi, size=(n, 2))
    distractor_radii = rng.uniform(0.18, 0.80, size=(n, 2))
    near_anchor = np.where(rng.random(size=(n, 1)) < 0.55, object_a, object_b)
    object_c = np.clip(
        near_anchor
        + np.column_stack([np.cos(distractor_angles[:, 0]), np.sin(distractor_angles[:, 0])])
        * distractor_radii[:, :1],
        -0.95,
        0.95,
    )
    object_d = rng.uniform(-0.95, 0.95, size=(n, 2))
    states = np.column_stack([object_a, object_b, object_c, object_d])
    actions_table = _object_actions()
    action_ids = rng.integers(0, actions_table.shape[0], size=n)
    actions = actions_table[action_ids]
    return {
        "states": states,
        "pixels": _render_multi_object_slots(states, object_count=4),
        "actions": actions,
        "next_states": _multi_object_step(states, actions),
        "contact": _multi_object_contact_after_action(states, actions),
        "gap": _multi_object_gap_after_action(states, actions),
    }


def _fit_object_counterfactual_model(states: np.ndarray, actions: np.ndarray, labels: np.ndarray) -> LinearHead:
    next_delta = states[:, :2] + actions - states[:, 2:]
    next_dist_sq = np.sum(next_delta * next_delta, axis=1, keepdims=True)
    features = np.column_stack(
        [
            states,
            actions,
            states[:, :2] - states[:, 2:],
            next_delta,
            next_dist_sq,
        ]
    )
    return _fit_head(features, labels)


def _object_counterfactual_scores(head: LinearHead, states: np.ndarray, actions: np.ndarray) -> np.ndarray:
    next_delta = states[:, :2] + actions - states[:, 2:]
    next_dist_sq = np.sum(next_delta * next_delta, axis=1, keepdims=True)
    features = np.column_stack(
        [
            states,
            actions,
            states[:, :2] - states[:, 2:],
            next_delta,
            next_dist_sq,
        ]
    )
    return head.score(features)


def _distractor_shifted_states(states: np.ndarray) -> np.ndarray:
    shifted = states.copy()
    shifted[:, 4:6] = np.clip(shifted[:, 4:6] + np.array([0.45, -0.35]), -0.95, 0.95)
    shifted[:, 6:8] = np.clip(shifted[:, 6:8] + np.array([-0.35, 0.45]), -0.95, 0.95)
    return shifted


def _fit_pixel_action_probe(pixels: np.ndarray, actions: np.ndarray, labels: np.ndarray) -> LinearHead:
    return _fit_head(np.column_stack([pixels, actions]), labels)


def _pixel_action_scores(head: LinearHead, pixels: np.ndarray, actions: np.ndarray) -> np.ndarray:
    return head.score(np.column_stack([pixels, actions]))


def _run_object_intervention_benchmark(*, train_seed: int = 505, test_seed: int = 606) -> dict[str, object]:
    train = _make_object_intervention_data(2200, seed=train_seed)
    test = _make_object_intervention_data(1000, seed=test_seed)
    latent_readout = _fit_latent_readout(train["pixels"], train["states"])
    train_latent = latent_readout.transform(train["pixels"])
    test_latent = latent_readout.transform(test["pixels"])

    posthoc_probe = _fit_pixel_action_probe(train["pixels"], train["actions"], train["contact"])
    s2_scores = _pixel_action_scores(posthoc_probe, test["pixels"], test["actions"])
    counterfactual_head = _fit_object_counterfactual_model(train_latent, train["actions"], train["contact"])
    s3_scores = _object_counterfactual_scores(counterfactual_head, test_latent, test["actions"])

    s2_gap = _margin_gap_score(s2_scores)
    s3_gap = np.maximum(_object_gap_score(test_latent, test["actions"]), _margin_gap_score(s3_scores))
    object_batch = BoundaryGatedBatch(
        z=test["states"],
        z_pair=test["next_states"],
        x=test["pixels"],
        x_pair=_render_object_slots(test["next_states"]),
        distinction=test["contact"],
        distinction_pair=_object_contact_after_action(test["next_states"], test["actions"]),
        gap=test["gap"],
        gap_pair=_object_gap_after_action(test["next_states"], test["actions"]),
        radius=0.34,
        gap_width=0.08,
    )
    systems = {
        "S2": _evaluate_system(
            SystemPrediction("S2", "posthoc-object-report", test["pixels"], s2_scores, s2_gap),
            object_batch,
            test["contact"],
            test["gap"],
        ),
        "S3": _evaluate_system(
            SystemPrediction("S3", "trained-object-bedc-jepa", test_latent, s3_scores, s3_gap),
            object_batch,
            test["contact"],
            test["gap"],
        ),
    }
    masked_pixels = test["pixels"].copy()
    slot_size = masked_pixels.shape[1] // 2
    masked_pixels[:, slot_size:] = 0.0
    masked_latent = latent_readout.transform(masked_pixels)
    masked_scores = _object_counterfactual_scores(counterfactual_head, masked_latent, test["actions"])
    masked_accuracy = binary_accuracy(masked_scores, test["contact"])
    unmasked_accuracy = binary_accuracy(s3_scores, test["contact"])
    masked_gap_scores = np.maximum(_object_gap_score(test_latent, test["actions"]), 1.0 - masked_accuracy)
    action_table = _object_actions()
    all_action_scores = [
        _object_counterfactual_scores(
            counterfactual_head,
            test_latent,
            np.repeat(action[None, :], test_latent.shape[0], axis=0),
        )
        for action in action_table
    ]
    action_score_matrix = np.column_stack(all_action_scores)
    return {
        "source": {
            "name": "two-object-counterfactual-contact-world",
            "observation": "two-object-pixel-slots",
            "query": "counterfactual-contact-after-action",
            "train_seed": float(train_seed),
            "test_seed": float(test_seed),
            "train_count": float(train["states"].shape[0]),
            "test_count": float(test["states"].shape[0]),
        },
        "transition": {
            "counterfactual_accuracy": binary_accuracy(s3_scores, test["contact"]),
            "intervention_sensitivity": float(np.mean(np.max(action_score_matrix, axis=1) - np.min(action_score_matrix, axis=1))),
        },
        "systems": systems,
        "object_masking": {
            "masked_object_accuracy_drop": float(unmasked_accuracy - masked_accuracy),
            "gap_auc_under_mask": gap_detection_auc(masked_gap_scores, test["gap"]),
        },
    }


def _run_object_intervention_sweep() -> dict[str, float]:
    results = [
        _run_object_intervention_benchmark(train_seed=3000 + seed * 17, test_seed=4000 + seed * 19)
        for seed in range(8)
    ]
    outside_gap_delta = []
    gap_auc_delta = []
    unlogged_delta = []
    debt_delta = []
    counterfactual_accuracy = []
    intervention_sensitivity = []
    mask_drop = []
    for result in results:
        s2 = result["systems"]["S2"]
        s3 = result["systems"]["S3"]
        outside_gap_delta.append(float(s3["distinction_accuracy_outside_gap"]) - float(s2["distinction_accuracy_outside_gap"]))
        gap_auc_delta.append(float(s3["gap_detection_auc"]) - float(s2["gap_detection_auc"]))
        unlogged_delta.append(float(s2["unlogged_error_rate"]) - float(s3["unlogged_error_rate"]))
        debt_delta.append(float(s2["bedc_debt_score"]) - float(s3["bedc_debt_score"]))
        counterfactual_accuracy.append(float(result["transition"]["counterfactual_accuracy"]))
        intervention_sensitivity.append(float(result["transition"]["intervention_sensitivity"]))
        mask_drop.append(float(result["object_masking"]["masked_object_accuracy_drop"]))
    return {
        "seed_count": float(len(results)),
        "s3_minus_s2_outside_gap_accuracy_mean": _mean(outside_gap_delta),
        "s3_minus_s2_outside_gap_accuracy_ci95": _confidence_radius(outside_gap_delta),
        "s3_minus_s2_gap_auc_mean": _mean(gap_auc_delta),
        "s3_minus_s2_gap_auc_ci95": _confidence_radius(gap_auc_delta),
        "s2_minus_s3_unlogged_error_mean": _mean(unlogged_delta),
        "s2_minus_s3_unlogged_error_ci95": _confidence_radius(unlogged_delta),
        "s2_minus_s3_debt_mean": _mean(debt_delta),
        "s2_minus_s3_debt_ci95": _confidence_radius(debt_delta),
        "s3_better_outside_gap_accuracy_rate": _mean([1.0 if value > 0.0 else 0.0 for value in outside_gap_delta]),
        "s3_better_gap_auc_rate": _mean([1.0 if value > 0.0 else 0.0 for value in gap_auc_delta]),
        "s3_better_unlogged_error_rate": _mean([1.0 if value > 0.0 else 0.0 for value in unlogged_delta]),
        "s3_better_debt_rate": _mean([1.0 if value > 0.0 else 0.0 for value in debt_delta]),
        "counterfactual_accuracy_mean": _mean(counterfactual_accuracy),
        "counterfactual_accuracy_ci95": _confidence_radius(counterfactual_accuracy),
        "intervention_sensitivity_mean": _mean(intervention_sensitivity),
        "intervention_sensitivity_ci95": _confidence_radius(intervention_sensitivity),
        "masked_object_accuracy_drop_mean": _mean(mask_drop),
        "masked_object_accuracy_drop_ci95": _confidence_radius(mask_drop),
    }


def _run_multi_object_distractor_benchmark(*, train_seed: int = 707, test_seed: int = 808) -> dict[str, object]:
    train = _make_multi_object_distractor_data(2800, seed=train_seed)
    test = _make_multi_object_distractor_data(1200, seed=test_seed)
    latent_readout = _fit_latent_readout(train["pixels"], train["states"])
    train_latent = latent_readout.transform(train["pixels"])
    test_latent = latent_readout.transform(test["pixels"])

    posthoc_probe = _fit_pixel_action_probe(train["pixels"], train["actions"], train["contact"])
    s2_scores = _pixel_action_scores(posthoc_probe, test["pixels"], test["actions"])
    counterfactual_head = _fit_object_counterfactual_model(
        _multi_object_target_pair(train_latent),
        train["actions"],
        train["contact"],
    )
    s3_scores = _object_counterfactual_scores(
        counterfactual_head,
        _multi_object_target_pair(test_latent),
        test["actions"],
    )

    s2_gap = _margin_gap_score(s2_scores)
    s3_gap = np.maximum(
        _multi_object_gap_score(test_latent, test["actions"]),
        _margin_gap_score(s3_scores),
    )
    object_batch = BoundaryGatedBatch(
        z=test["states"],
        z_pair=test["next_states"],
        x=test["pixels"],
        x_pair=_render_multi_object_slots(test["next_states"], object_count=4),
        distinction=test["contact"],
        distinction_pair=_multi_object_contact_after_action(test["next_states"], test["actions"]),
        gap=test["gap"],
        gap_pair=_multi_object_gap_after_action(test["next_states"], test["actions"]),
        radius=0.34,
        gap_width=0.08,
    )
    systems = {
        "S2": _evaluate_system(
            SystemPrediction("S2", "posthoc-multi-object-report", test["pixels"], s2_scores, s2_gap),
            object_batch,
            test["contact"],
            test["gap"],
        ),
        "S3": _evaluate_system(
            SystemPrediction("S3", "trained-multi-object-bedc-jepa", test_latent, s3_scores, s3_gap),
            object_batch,
            test["contact"],
            test["gap"],
        ),
    }

    slot_size = test["pixels"].shape[1] // 4
    target_masked_pixels = test["pixels"].copy()
    target_masked_pixels[:, slot_size : 2 * slot_size] = 0.0
    target_masked_latent = latent_readout.transform(target_masked_pixels)
    target_masked_scores = _object_counterfactual_scores(
        counterfactual_head,
        _multi_object_target_pair(target_masked_latent),
        test["actions"],
    )
    distractor_masked_pixels = test["pixels"].copy()
    distractor_masked_pixels[:, 2 * slot_size :] = 0.0
    distractor_masked_latent = latent_readout.transform(distractor_masked_pixels)
    distractor_masked_scores = _object_counterfactual_scores(
        counterfactual_head,
        _multi_object_target_pair(distractor_masked_latent),
        test["actions"],
    )
    unmasked_accuracy = binary_accuracy(s3_scores, test["contact"])
    shifted_states = _distractor_shifted_states(test["states"])
    shifted_scores = _object_counterfactual_scores(
        counterfactual_head,
        _multi_object_target_pair(shifted_states),
        test["actions"],
    )
    return {
        "source": {
            "name": "four-object-distractor-contact-world",
            "observation": "four-object-pixel-slots",
            "query": "target-pair-counterfactual-contact-after-action",
            "target_pair": "object-a-object-b",
            "distractor_count": 2,
            "train_seed": float(train_seed),
            "test_seed": float(test_seed),
            "train_count": float(train["states"].shape[0]),
            "test_count": float(test["states"].shape[0]),
        },
        "transition": {
            "counterfactual_accuracy": binary_accuracy(s3_scores, test["contact"]),
            "distractor_invariance": 1.0 - float(np.mean(np.abs(s3_scores - shifted_scores))),
        },
        "systems": systems,
        "object_masking": {
            "target_mask_accuracy_drop": float(unmasked_accuracy - binary_accuracy(target_masked_scores, test["contact"])),
            "distractor_mask_accuracy_drop": float(
                unmasked_accuracy - binary_accuracy(distractor_masked_scores, test["contact"])
            ),
        },
    }


def _run_multi_object_distractor_sweep() -> dict[str, float]:
    results = [
        _run_multi_object_distractor_benchmark(train_seed=5000 + seed * 23, test_seed=6000 + seed * 29)
        for seed in range(6)
    ]
    outside_gap_delta = []
    gap_auc_delta = []
    unlogged_delta = []
    debt_delta = []
    counterfactual_accuracy = []
    distractor_invariance = []
    mask_delta = []
    for result in results:
        s2 = result["systems"]["S2"]
        s3 = result["systems"]["S3"]
        masking = result["object_masking"]
        outside_gap_delta.append(float(s3["distinction_accuracy_outside_gap"]) - float(s2["distinction_accuracy_outside_gap"]))
        gap_auc_delta.append(float(s3["gap_detection_auc"]) - float(s2["gap_detection_auc"]))
        unlogged_delta.append(float(s2["unlogged_error_rate"]) - float(s3["unlogged_error_rate"]))
        debt_delta.append(float(s2["bedc_debt_score"]) - float(s3["bedc_debt_score"]))
        counterfactual_accuracy.append(float(result["transition"]["counterfactual_accuracy"]))
        distractor_invariance.append(float(result["transition"]["distractor_invariance"]))
        mask_delta.append(float(masking["target_mask_accuracy_drop"]) - float(masking["distractor_mask_accuracy_drop"]))
    return {
        "seed_count": float(len(results)),
        "s3_minus_s2_outside_gap_accuracy_mean": _mean(outside_gap_delta),
        "s3_minus_s2_outside_gap_accuracy_ci95": _confidence_radius(outside_gap_delta),
        "s3_minus_s2_gap_auc_mean": _mean(gap_auc_delta),
        "s3_minus_s2_gap_auc_ci95": _confidence_radius(gap_auc_delta),
        "s2_minus_s3_unlogged_error_mean": _mean(unlogged_delta),
        "s2_minus_s3_unlogged_error_ci95": _confidence_radius(unlogged_delta),
        "s2_minus_s3_debt_mean": _mean(debt_delta),
        "s2_minus_s3_debt_ci95": _confidence_radius(debt_delta),
        "s3_better_outside_gap_accuracy_rate": _mean([1.0 if value > 0.0 else 0.0 for value in outside_gap_delta]),
        "s3_better_gap_auc_rate": _mean([1.0 if value > 0.0 else 0.0 for value in gap_auc_delta]),
        "s3_better_unlogged_error_rate": _mean([1.0 if value > 0.0 else 0.0 for value in unlogged_delta]),
        "s3_better_debt_rate": _mean([1.0 if value > 0.0 else 0.0 for value in debt_delta]),
        "counterfactual_accuracy_mean": _mean(counterfactual_accuracy),
        "counterfactual_accuracy_ci95": _confidence_radius(counterfactual_accuracy),
        "distractor_invariance_mean": _mean(distractor_invariance),
        "distractor_invariance_ci95": _confidence_radius(distractor_invariance),
        "target_minus_distractor_mask_drop_mean": _mean(mask_delta),
        "target_minus_distractor_mask_drop_ci95": _confidence_radius(mask_delta),
    }


def run_bedc_jepa_experiment() -> dict[str, object]:
    train = make_boundary_gated_batch(1536, rho=0.84, radius=1.0, gap_width=0.14, seed=101)
    test = make_boundary_gated_batch(768, rho=0.84, radius=1.0, gap_width=0.14, seed=202)
    world = radial_world_spec(radius=train.radius, gap_width=train.gap_width)
    predictions = _fit_systems_for_world(train, test, world)
    test_distinction = world.distinction(test.z)
    test_gap = world.gap(test.z)
    systems = {
        code: _evaluate_system(prediction, test, test_distinction, test_gap)
        for code, prediction in predictions.items()
    }

    planning_initial = np.array(
        [
            [-1.4, -1.3],
            [-1.5, -0.8],
            [-1.2, -1.5],
            [-0.9, -1.4],
            [-1.6, -1.6],
            [-1.8, -0.9],
            [-0.8, -1.7],
            [-1.4, -1.8],
        ],
        dtype=np.float64,
    )
    planning = {
        "vanilla": _rollout_planner(
            initial_states=planning_initial,
            gap_score=world.gap_score,
            use_gap_penalty=False,
        ),
        "gap_aware": _rollout_planner(
            initial_states=planning_initial,
            gap_score=world.gap_score,
            use_gap_penalty=True,
        ),
    }

    return {
        "run_id": "bedc-jepa-four-system-boundary-world-seed-101-202",
        "source": {
            "name": "boundary-gated-ou-world",
            "train_count": float(train.z.shape[0]),
            "test_count": float(test.z.shape[0]),
            "rho": 0.84,
            "radius": train.radius,
            "gap_width": train.gap_width,
        },
        "systems": systems,
        "planning": planning,
        "seed_sweep": _run_seed_sweep(),
        "grid_transition": _run_grid_transition_benchmark(),
        "object_intervention": _run_object_intervention_benchmark(),
        "object_intervention_sweep": _run_object_intervention_sweep(),
        "multi_object_distractor": _run_multi_object_distractor_benchmark(),
        "multi_object_distractor_sweep": _run_multi_object_distractor_sweep(),
    }
