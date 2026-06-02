"""Native public MiniGrid benchmark packet for BEDC-JEPA evidence gates."""

from __future__ import annotations

from dataclasses import dataclass
import copy
import importlib.util
import json
from pathlib import Path
from typing import Any

import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import (
    bedc_debt_score,
    binary_accuracy,
    certified_coverage,
    false_claim_rate,
    gap_detection_auc,
    unlogged_error_rate,
)


SYSTEM_CODES = ("S0", "S1", "S2", "S3")
DEFAULT_ENVIRONMENT_ID = "MiniGrid-DoorKey-8x8-v0"
DEFAULT_SWEEP_SEEDS = (20260602, 20260603, 20260604, 20260605, 20260606)


@dataclass(frozen=True)
class _Head:
    weights: np.ndarray

    def score(self, features: np.ndarray) -> np.ndarray:
        logits = _design(features) @ self.weights
        return _sigmoid(logits)


@dataclass(frozen=True)
class _CalibratedHead:
    base: _Head
    threshold: float
    scale: float

    def score(self, features: np.ndarray) -> np.ndarray:
        raw = self.base.score(features)
        return _sigmoid(self.scale * (raw - self.threshold))


def _dependency_status() -> dict[str, str]:
    return {
        name: "installed" if importlib.util.find_spec(name) is not None else "missing"
        for name in ("gymnasium", "minigrid")
    }


def _sigmoid(values: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(values, -40.0, 40.0)))


def _design(features: np.ndarray) -> np.ndarray:
    if features.ndim != 2:
        raise ValueError("features must be a matrix")
    quadratic = features * features
    return np.column_stack([features, quadratic, np.ones(features.shape[0])])


def _fit_head(features: np.ndarray, labels: np.ndarray, *, ridge: float = 1e-3) -> _Head:
    labels_arr = np.asarray(labels, dtype=bool)
    target = np.where(labels_arr, 0.92, 0.08)
    logits = np.log(target / (1.0 - target))
    design = _design(features)
    gram = design.T @ design + ridge * np.eye(design.shape[1])
    rhs = design.T @ logits
    return _Head(np.linalg.solve(gram, rhs))


def _calibrate_gap_head(head: _Head, features: np.ndarray, labels: np.ndarray) -> _CalibratedHead:
    raw = head.score(features)
    positive_rate = float(np.mean(np.asarray(labels, dtype=bool)))
    quantile = max(0.05, min(0.95, 1.0 - positive_rate))
    threshold = float(np.quantile(raw, quantile))
    return _CalibratedHead(base=head, threshold=threshold, scale=8.0)


def _object_mask(image: Any, object_id: int) -> np.ndarray:
    array = np.asarray(image)
    return array[:, :, 0] == object_id


def _agent_position(image: Any) -> np.ndarray:
    mask = _object_mask(image, 10)
    if np.any(mask):
        return np.argwhere(mask)[0].astype(np.float64)
    return np.asarray([3.0, 6.0], dtype=np.float64)


def _distance_to_object(image: Any, object_id: int) -> float:
    mask = _object_mask(image, object_id)
    if not np.any(mask):
        return 10.0
    points = np.argwhere(mask).astype(np.float64)
    agent = _agent_position(image)
    return float(np.min(np.sum(np.abs(points - agent), axis=1)))


def _door_key_labels(image: Any) -> tuple[bool, bool]:
    key_visible = bool(np.any(_object_mask(image, 5)))
    door_visible = bool(np.any(_object_mask(image, 4)))
    goal_visible = bool(np.any(_object_mask(image, 8)))
    distinction = key_visible or door_visible or goal_visible
    nearest = min(
        _distance_to_object(image, 5),
        _distance_to_object(image, 4),
        _distance_to_object(image, 8),
    )
    low_context = distinction and not (key_visible and door_visible)
    near_boundary = nearest <= 2.0
    return distinction, bool(low_context or near_boundary)


def _feature_vector(image: Any, action: int, action_count: int) -> np.ndarray:
    array = np.asarray(image, dtype=np.float64)
    flat = array.reshape(-1) / 10.0
    key = float(np.any(_object_mask(image, 5)))
    door = float(np.any(_object_mask(image, 4)))
    goal = float(np.any(_object_mask(image, 8)))
    distances = np.asarray(
        [
            _distance_to_object(image, 5),
            _distance_to_object(image, 4),
            _distance_to_object(image, 8),
        ],
        dtype=np.float64,
    )
    distances = distances / 10.0
    one_hot = np.zeros(action_count, dtype=np.float64)
    one_hot[int(action)] = 1.0
    visible = np.asarray([key, door, goal], dtype=np.float64)
    return np.concatenate([flat, visible, distances, one_hot, visible.repeat(action_count) * np.tile(one_hot, 3)])


def _margin_gap_score(scores: np.ndarray) -> np.ndarray:
    margin = np.abs(np.asarray(scores, dtype=np.float64) - 0.5)
    return _sigmoid(14.0 * (0.10 - margin))


def _system_metrics(distinction_scores: np.ndarray, gap_scores: np.ndarray, labels: np.ndarray, gaps: np.ndarray) -> dict[str, float]:
    gap_auc = gap_detection_auc(gap_scores, gaps)
    false_claim = false_claim_rate(distinction_scores, labels, gaps)
    unlogged = unlogged_error_rate(distinction_scores, labels, gap_scores)
    certified = certified_coverage(gap_scores)
    return {
        "distinction_accuracy": binary_accuracy(distinction_scores, labels),
        "gap_detection_auc": gap_auc,
        "unlogged_error_rate": unlogged,
        "certified_coverage": certified,
        "bedc_debt_score": bedc_debt_score(
            unlogged_error=unlogged,
            false_claim=false_claim,
            gap_auc=gap_auc,
            certified=certified,
        ),
    }


def _unavailable_packet(
    *,
    environment_id: str,
    sample_count: int,
    planning_state_count: int,
    seed: int,
    deps: dict[str, str],
) -> dict[str, Any]:
    return {
        "schema_id": "bedc-jepa-public-native-minigrid-benchmark",
        "status": "unavailable",
        "environment_id": environment_id,
        "seed": float(seed),
        "sample_count_requested": float(sample_count),
        "sample_count_collected": 0.0,
        "planning_state_count_requested": float(planning_state_count),
        "planning_state_count_collected": 0.0,
        "dependency_status": deps,
        "systems": {},
        "planning_lambda_sweep": [],
        "jepa_family_baseline_boundary": {
            "status": "unavailable",
            "candidate_id": "public-minigrid-jepa-style-s0",
        },
        "cannot_claim": ["native public MiniGrid benchmark was not executed in this environment"],
    }


def _collect_examples(
    *,
    environment_id: str,
    sample_count: int,
    planning_state_count: int,
    seed: int,
) -> tuple[dict[str, np.ndarray], list[dict[str, Any]], int]:
    import gymnasium as gym
    import minigrid  # noqa: F401

    env = gym.make(environment_id)
    try:
        observation, _ = env.reset(seed=seed)
        action_count = int(env.action_space.n)
        rng = np.random.default_rng(seed)
        features = []
        labels = []
        gaps = []
        planning_states: list[dict[str, Any]] = []
        for index in range(sample_count):
            action = int(rng.integers(action_count))
            image = observation["image"]
            next_observation, _, terminated, truncated, _ = env.step(action)
            distinction, gap = _door_key_labels(next_observation["image"])
            features.append(_feature_vector(image, action, action_count))
            labels.append(distinction)
            gaps.append(gap)

            if len(planning_states) < planning_state_count:
                candidate_features = []
                candidate_labels = []
                candidate_gaps = []
                plan_actions = []
                for first_action in range(action_count):
                    for second_action in range(action_count):
                        branch = copy.deepcopy(env)
                        try:
                            first_observation, _, first_done, first_truncated, _ = branch.step(first_action)
                            second_observation = first_observation
                            if not (first_done or first_truncated):
                                second_observation, _, _, _, _ = branch.step(second_action)
                            first_distinction, first_gap = _door_key_labels(first_observation["image"])
                            second_distinction, second_gap = _door_key_labels(second_observation["image"])
                        finally:
                            branch.close()
                        candidate_features.append(_feature_vector(image, first_action, action_count))
                        candidate_labels.append(bool(first_distinction or second_distinction))
                        candidate_gaps.append(bool(first_gap or second_gap))
                        plan_actions.append([float(first_action), float(second_action)])
                planning_states.append(
                    {
                        "features": np.asarray(candidate_features, dtype=np.float64),
                        "labels": np.asarray(candidate_labels, dtype=bool),
                        "gaps": np.asarray(candidate_gaps, dtype=bool),
                        "plan_actions": plan_actions,
                    }
                )

            observation = next_observation
            if terminated or truncated:
                observation, _ = env.reset(seed=seed + index + 1)
        return (
            {
                "features": np.asarray(features, dtype=np.float64),
                "labels": np.asarray(labels, dtype=bool),
                "gaps": np.asarray(gaps, dtype=bool),
            },
            planning_states,
            action_count,
        )
    finally:
        env.close()


def _evaluate_systems(train: dict[str, np.ndarray], test: dict[str, np.ndarray]) -> tuple[dict[str, Any], dict[str, _Head]]:
    distinction_head = _fit_head(train["features"], train["labels"])
    gap_head = _calibrate_gap_head(_fit_head(train["features"], train["gaps"]), train["features"], train["gaps"])
    s0_scores = np.full(test["labels"].shape[0], float(np.mean(train["labels"])), dtype=np.float64)
    s1_scores = distinction_head.score(test["features"])
    s2_gap = _margin_gap_score(s1_scores)
    s3_gap = gap_head.score(test["features"])
    systems = {
        "S0": {
            "system_name": "public-minigrid-jepa-style-latent-only",
            "changes_training_objective": 0.0,
            **_system_metrics(s0_scores, np.zeros_like(s0_scores), test["labels"], test["gaps"]),
        },
        "S1": {
            "system_name": "public-minigrid-posthoc-probe",
            "changes_training_objective": 0.0,
            **_system_metrics(s1_scores, np.zeros_like(s1_scores), test["labels"], test["gaps"]),
        },
        "S2": {
            "system_name": "public-minigrid-posthoc-evidence-envelope",
            "changes_training_objective": 0.0,
            **_system_metrics(s1_scores, s2_gap, test["labels"], test["gaps"]),
        },
        "S3": {
            "system_name": "public-minigrid-trained-bedc-jepa-readout",
            "changes_training_objective": 1.0,
            **_system_metrics(s1_scores, s3_gap, test["labels"], test["gaps"]),
        },
    }
    return systems, {"distinction": distinction_head, "gap": gap_head}


def _planning_sweep(planning_states: list[dict[str, Any]], heads: dict[str, Any], lambdas: tuple[float, ...]) -> list[dict[str, float]]:
    rows = []
    for lam in lambdas:
        successes = []
        high_gaps = []
        costs = []
        for state in planning_states:
            distinction_scores = heads["distinction"].score(state["features"])
            gap_scores = np.where(np.asarray(state["gaps"], dtype=bool), 1.0, 0.0)
            objective = distinction_scores - float(lam) * gap_scores
            selected = int(np.argmax(objective))
            success = bool(state["labels"][selected])
            high_gap = bool(state["gaps"][selected])
            successes.append(success)
            high_gaps.append(high_gap)
            costs.append((0.0 if success else 1.0) + float(lam) * (1.0 if high_gap else 0.0))
        rows.append(
            {
                "lambda_g": float(lam),
                "planning_state_count": float(len(planning_states)),
                "success_rate": float(np.mean(successes)) if successes else 0.0,
                "high_gap_state_rate": float(np.mean(high_gaps)) if high_gaps else 0.0,
                "risk_adjusted_cost": float(np.mean(costs)) if costs else 0.0,
            }
        )
    return rows


def _planning_deltas(planning: list[dict[str, float]]) -> dict[str, float]:
    if not planning:
        return {
            "lambda_0_minus_best_high_gap_rate": 0.0,
            "lambda_0_minus_best_success_rate": 0.0,
            "best_planning_lambda_g": 0.0,
        }
    baseline = planning[0]
    best = min(planning, key=lambda row: (row["high_gap_state_rate"], row["risk_adjusted_cost"]))
    return {
        "lambda_0_minus_best_high_gap_rate": float(baseline["high_gap_state_rate"]) - float(best["high_gap_state_rate"]),
        "lambda_0_minus_best_success_rate": float(baseline["success_rate"]) - float(best["success_rate"]),
        "best_planning_lambda_g": float(best["lambda_g"]),
    }


def build_public_minigrid_native_benchmark(
    *,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
    train_count: int = 128,
    test_count: int = 128,
    planning_state_count: int = 32,
    seed: int = 20260602,
) -> dict[str, Any]:
    deps = _dependency_status()
    sample_count = train_count + test_count
    if not all(status == "installed" for status in deps.values()):
        return _unavailable_packet(
            environment_id=environment_id,
            sample_count=sample_count,
            planning_state_count=planning_state_count,
            seed=seed,
            deps=deps,
        )

    train, _, action_count = _collect_examples(
        environment_id=environment_id,
        sample_count=train_count,
        planning_state_count=0,
        seed=seed,
    )
    test, planning_states, _ = _collect_examples(
        environment_id=environment_id,
        sample_count=test_count,
        planning_state_count=planning_state_count,
        seed=seed + 1,
    )
    systems, heads = _evaluate_systems(train, test)
    planning = _planning_sweep(planning_states, heads, (0.0, 0.5, 1.0, 2.0, 4.0))
    planning_deltas = _planning_deltas(planning)
    s0 = systems["S0"]
    s3 = systems["S3"]
    return {
        "schema_id": "bedc-jepa-public-native-minigrid-benchmark",
        "status": "executed",
        "environment_id": environment_id,
        "benchmark_contract": "native-public-minigrid-doorkey-action-conditioned-readback",
        "seed": float(seed),
        "sample_count_requested": float(sample_count),
        "sample_count_collected": float(sample_count),
        "train_count": float(train_count),
        "test_count": float(test_count),
        "planning_state_count_requested": float(planning_state_count),
        "planning_state_count_collected": float(len(planning_states)),
        "observation_contract": "MiniGrid image observation, shape 7x7x3",
        "action_contract": f"MiniGrid discrete action id, action_count={action_count}",
        "input_contract": "current public MiniGrid image plus candidate action predicts next DoorKey readback and gap labels",
        "dependency_status": deps,
        "systems": systems,
        "planning_contract": "two-step public MiniGrid candidate plans selected by distinction readout minus lambda times audited plan outcome gap label",
        "planning_lambda_sweep": planning,
        "jepa_family_baseline_boundary": {
            "status": "executed",
            "candidate_id": "public-minigrid-jepa-style-s0",
            "baseline_role": "latent/prediction-only JEPA-style control row on the same public observation/action stream",
            "reported_benchmark_name": environment_id,
            "latent_prediction_score": float(s0["distinction_accuracy"]),
            "rollout_or_planning_score": float(planning[0]["success_rate"]) if planning else 0.0,
            "comparison_scope": "same public MiniGrid observation/action stream; no public benchmark superiority claim",
        },
        "deltas": {
            "s3_minus_s0_distinction_accuracy": float(s3["distinction_accuracy"]) - float(s0["distinction_accuracy"]),
            "s3_minus_s0_gap_auc": float(s3["gap_detection_auc"]) - float(s0["gap_detection_auc"]),
            "s0_minus_s3_unlogged_error": float(s0["unlogged_error_rate"]) - float(s3["unlogged_error_rate"]),
            "s0_minus_s3_debt": float(s0["bedc_debt_score"]) - float(s3["bedc_debt_score"]),
            **planning_deltas,
        },
        "cannot_claim": [
            "public benchmark superiority",
            "native V-JEPA2-AC checkpoint reproduction",
            "robotics benchmark result",
            "large-scale real-world conclusion",
            "formal neural-network proof",
        ],
    }


def write_public_minigrid_native_benchmark(path: str | Path) -> dict[str, Any]:
    packet = build_public_minigrid_native_benchmark()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def _mean_std(values: list[float]) -> dict[str, float]:
    arr = np.asarray(values, dtype=np.float64)
    return {
        "mean": float(np.mean(arr)) if arr.size else 0.0,
        "std": float(np.std(arr, ddof=0)) if arr.size else 0.0,
    }


def _win_rate(values: list[float], *, threshold: float = 0.0) -> float:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return 0.0
    return float(np.mean(arr > threshold))


def build_public_minigrid_native_seed_sweep(
    *,
    seeds: tuple[int, ...] = DEFAULT_SWEEP_SEEDS,
    train_count: int = 128,
    test_count: int = 128,
    planning_state_count: int = 32,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
) -> dict[str, Any]:
    packets = [
        build_public_minigrid_native_benchmark(
            environment_id=environment_id,
            train_count=train_count,
            test_count=test_count,
            planning_state_count=planning_state_count,
            seed=seed,
        )
        for seed in seeds
    ]
    executed = [packet for packet in packets if packet.get("status") == "executed"]
    if len(executed) != len(packets):
        return {
            "schema_id": "bedc-jepa-public-native-minigrid-seed-sweep",
            "status": "unavailable",
            "environment_id": environment_id,
            "seed_count_requested": float(len(seeds)),
            "seed_count_executed": float(len(executed)),
            "seeds": [float(seed) for seed in seeds],
            "packets": packets,
            "summary": {},
            "cannot_claim": ["native public MiniGrid seed sweep was not fully executed in this environment"],
        }

    delta_keys = [
        "s0_minus_s3_unlogged_error",
        "s3_minus_s0_gap_auc",
        "s0_minus_s3_debt",
        "lambda_0_minus_best_high_gap_rate",
        "lambda_0_minus_best_success_rate",
    ]
    summary = {
        f"{key}_{stat}": value
        for key in delta_keys
        for stat, value in _mean_std([float(packet["deltas"][key]) for packet in executed]).items()
    }
    summary.update(
        {
            "seed_count": float(len(executed)),
            "unlogged_error_win_rate": _win_rate([float(packet["deltas"]["s0_minus_s3_unlogged_error"]) for packet in executed]),
            "gap_auc_win_rate": _win_rate([float(packet["deltas"]["s3_minus_s0_gap_auc"]) for packet in executed]),
            "debt_win_rate": _win_rate([float(packet["deltas"]["s0_minus_s3_debt"]) for packet in executed]),
            "planning_high_gap_reduction_win_rate": _win_rate(
                [float(packet["deltas"]["lambda_0_minus_best_high_gap_rate"]) for packet in executed]
            ),
        }
    )
    return {
        "schema_id": "bedc-jepa-public-native-minigrid-seed-sweep",
        "status": "executed",
        "environment_id": environment_id,
        "seed_count_requested": float(len(seeds)),
        "seed_count_executed": float(len(executed)),
        "seeds": [float(seed) for seed in seeds],
        "train_count": float(train_count),
        "test_count": float(test_count),
        "planning_state_count": float(planning_state_count),
        "summary": summary,
        "packets": packets,
        "cannot_claim": [
            "public benchmark superiority",
            "native V-JEPA2-AC checkpoint reproduction",
            "robotics benchmark result",
            "large-scale real-world conclusion",
        ],
    }


def write_public_minigrid_native_seed_sweep(path: str | Path) -> dict[str, Any]:
    packet = build_public_minigrid_native_seed_sweep()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet
