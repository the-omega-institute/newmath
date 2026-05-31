"""Optional adapter for public MiniGrid-family environments."""

from __future__ import annotations

from dataclasses import dataclass, asdict
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


@dataclass(frozen=True)
class PublicMiniGridProbe:
    status: str
    environment_id: str
    observation_contract: str
    action_contract: str
    dependency_status: dict[str, str]
    benchmark_role: str
    cannot_claim: list[str]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def write_json(self, path: str | Path) -> None:
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(self.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _dependency_status() -> dict[str, str]:
    status = {}
    for name in ("gymnasium", "minigrid"):
        status[name] = "installed" if importlib.util.find_spec(name) is not None else "missing"
    return status


def build_public_minigrid_probe(environment_id: str = "MiniGrid-DoorKey-8x8-v0") -> PublicMiniGridProbe:
    deps = _dependency_status()
    available = all(value == "installed" for value in deps.values())
    return PublicMiniGridProbe(
        status="available" if available else "unavailable",
        environment_id=environment_id,
        observation_contract="Gymnasium reset/step observation with MiniGrid image channel",
        action_contract="Discrete MiniGrid action ids; adapter maps them to transition samples",
        dependency_status=deps,
        benchmark_role="public visual navigation benchmark adapter for BEDC-JEPA planning claims",
        cannot_claim=[] if available else ["public MiniGrid run was not executed in this environment"],
    )


def write_public_minigrid_probe(path: str | Path) -> PublicMiniGridProbe:
    probe = build_public_minigrid_probe()
    probe.write_json(path)
    return probe


def write_public_minigrid_transition_packet(path: str | Path) -> dict[str, Any]:
    packet = build_public_minigrid_transition_packet()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def _image_checksum(image: Any) -> float:
    array = np.asarray(image, dtype=np.float64)
    weights = np.arange(1, array.size + 1, dtype=np.float64).reshape(array.shape)
    return float(np.sum(array * weights))


def _unavailable_transition_packet(
    *,
    environment_id: str,
    sample_count: int,
    seed: int,
    deps: dict[str, str],
) -> dict[str, Any]:
    return {
        "status": "unavailable",
        "environment_id": environment_id,
        "seed": float(seed),
        "sample_count_requested": float(sample_count),
        "sample_count_collected": 0.0,
        "observation_key": "image",
        "observation_shape_contract": [7.0, 7.0, 3.0],
        "action_space_contract": "Discrete",
        "dependency_status": deps,
        "transition_samples": [],
        "cannot_claim": ["public MiniGrid run was not executed in this environment"],
    }


def _empty_metric_packet() -> dict[str, None]:
    return {
        "distinction_accuracy": None,
        "gap_detection_auc": None,
        "unlogged_error_rate": None,
        "certified_coverage": None,
        "bedc_debt_score": None,
    }


def _unavailable_benchmark_packet(
    *,
    environment_id: str,
    sample_count: int,
    seed: int,
    deps: dict[str, str],
) -> dict[str, Any]:
    return {
        "status": "unavailable",
        "environment_id": environment_id,
        "benchmark_contract": "door-key-public-readback-gap",
        "seed": float(seed),
        "sample_count_requested": float(sample_count),
        "sample_count_collected": 0.0,
        "observation_key": "image",
        "observation_shape_contract": [7.0, 7.0, 3.0],
        "action_space_contract": "Discrete",
        "dependency_status": deps,
        "metrics": _empty_metric_packet(),
        "cannot_claim": ["public MiniGrid benchmark was not executed in this environment"],
    }


def build_public_minigrid_transition_packet(
    *,
    environment_id: str = "MiniGrid-DoorKey-8x8-v0",
    sample_count: int = 32,
    seed: int = 20260531,
) -> dict[str, Any]:
    deps = _dependency_status()
    if not all(value == "installed" for value in deps.values()):
        return _unavailable_transition_packet(
            environment_id=environment_id,
            sample_count=sample_count,
            seed=seed,
            deps=deps,
        )

    import gymnasium as gym
    import minigrid  # noqa: F401

    env = gym.make(environment_id)
    try:
        observation, _ = env.reset(seed=seed)
        rng = np.random.default_rng(seed)
        samples = []
        for index in range(sample_count):
            image = observation["image"]
            action = int(rng.integers(env.action_space.n))
            next_observation, reward, terminated, truncated, _ = env.step(action)
            next_image = next_observation["image"]
            samples.append(
                {
                    "index": float(index),
                    "action": float(action),
                    "reward": float(reward),
                    "terminated": bool(terminated),
                    "truncated": bool(truncated),
                    "image_checksum": _image_checksum(image),
                    "next_image_checksum": _image_checksum(next_image),
                }
            )
            observation = next_observation
            if terminated or truncated:
                observation, _ = env.reset(seed=seed + index + 1)
        return {
            "status": "available",
            "environment_id": environment_id,
            "seed": float(seed),
            "sample_count_requested": float(sample_count),
            "sample_count_collected": float(len(samples)),
            "observation_key": "image",
            "observation_shape_contract": [7.0, 7.0, 3.0],
            "action_space_contract": "Discrete",
            "dependency_status": deps,
            "transition_samples": samples,
            "cannot_claim": [],
        }
    finally:
        env.close()


def _visible_object_mask(image: Any, object_ids: set[int]) -> np.ndarray:
    array = np.asarray(image)
    return np.isin(array[:, :, 0], list(object_ids))


def _agent_position(image: Any) -> np.ndarray:
    array = np.asarray(image)
    mask = array[:, :, 0] == 10
    if np.any(mask):
        return np.argwhere(mask)[0].astype(np.float64)
    return np.asarray([3.0, 6.0], dtype=np.float64)


def _min_distance_to_mask(image: Any, object_ids: set[int]) -> float:
    mask = _visible_object_mask(image, object_ids)
    if not np.any(mask):
        return 10.0
    agent = _agent_position(image)
    points = np.argwhere(mask).astype(np.float64)
    return float(np.min(np.sum(np.abs(points - agent), axis=1)))


def _door_key_scores(image: Any) -> tuple[float, bool, float, bool]:
    key_visible = bool(np.any(_visible_object_mask(image, {5})))
    door_visible = bool(np.any(_visible_object_mask(image, {4})))
    goal_visible = bool(np.any(_visible_object_mask(image, {8})))
    target_visible = key_visible or door_visible or goal_visible
    key_distance = _min_distance_to_mask(image, {5})
    door_distance = _min_distance_to_mask(image, {4})
    goal_distance = _min_distance_to_mask(image, {8})
    nearest_distance = min(key_distance, door_distance, goal_distance)
    distinction_score = 1.0 if target_visible else 0.0
    low_context = not (key_visible and door_visible)
    near_boundary = nearest_distance <= 2.0
    gap_label = low_context or near_boundary
    gap_score = 0.85 if gap_label else 0.15
    return distinction_score, target_visible, gap_score, gap_label


def build_public_minigrid_benchmark_packet(
    *,
    environment_id: str = "MiniGrid-DoorKey-8x8-v0",
    sample_count: int = 32,
    seed: int = 20260531,
) -> dict[str, Any]:
    deps = _dependency_status()
    if not all(value == "installed" for value in deps.values()):
        return _unavailable_benchmark_packet(
            environment_id=environment_id,
            sample_count=sample_count,
            seed=seed,
            deps=deps,
        )

    import gymnasium as gym
    import minigrid  # noqa: F401

    env = gym.make(environment_id)
    try:
        observation, _ = env.reset(seed=seed)
        rng = np.random.default_rng(seed)
        distinction_scores = []
        distinction_labels = []
        gap_scores = []
        gap_labels = []
        for index in range(sample_count):
            d_score, d_label, g_score, g_label = _door_key_scores(observation["image"])
            distinction_scores.append(d_score)
            distinction_labels.append(d_label)
            gap_scores.append(g_score)
            gap_labels.append(g_label)
            action = int(rng.integers(env.action_space.n))
            observation, _, terminated, truncated, _ = env.step(action)
            if terminated or truncated:
                observation, _ = env.reset(seed=seed + index + 1)
        d_scores = np.asarray(distinction_scores, dtype=np.float64)
        d_labels = np.asarray(distinction_labels, dtype=bool)
        g_scores = np.asarray(gap_scores, dtype=np.float64)
        g_labels = np.asarray(gap_labels, dtype=bool)
        false_claim = false_claim_rate(d_scores, d_labels, g_labels)
        gap_auc = gap_detection_auc(g_scores, g_labels)
        unlogged = unlogged_error_rate(d_scores, d_labels, g_scores)
        certified = certified_coverage(g_scores)
        return {
            "status": "available",
            "environment_id": environment_id,
            "benchmark_contract": "door-key-public-readback-gap",
            "seed": float(seed),
            "sample_count_requested": float(sample_count),
            "sample_count_collected": float(sample_count),
            "observation_key": "image",
            "observation_shape_contract": [7.0, 7.0, 3.0],
            "action_space_contract": "Discrete",
            "dependency_status": deps,
            "metrics": {
                "distinction_accuracy": binary_accuracy(d_scores, d_labels),
                "gap_detection_auc": gap_auc,
                "unlogged_error_rate": unlogged,
                "certified_coverage": certified,
                "bedc_debt_score": bedc_debt_score(
                    unlogged_error=unlogged,
                    false_claim=false_claim,
                    gap_auc=gap_auc,
                    certified=certified,
                ),
            },
            "cannot_claim": [],
        }
    finally:
        env.close()


def import_public_minigrid_benchmark_metrics(result: dict[str, Any]) -> dict[str, Any]:
    required = {
        "environment_id",
        "seed",
        "sample_count_requested",
        "sample_count_collected",
        "distinction_accuracy",
        "gap_detection_auc",
        "unlogged_error_rate",
        "certified_coverage",
        "bedc_debt_score",
    }
    missing = sorted(required - set(result))
    if missing:
        raise ValueError(f"missing public MiniGrid benchmark result fields: {', '.join(missing)}")
    environment_id = str(result["environment_id"])
    if environment_id != "MiniGrid-DoorKey-8x8-v0":
        raise ValueError(f"unsupported public MiniGrid environment: {environment_id}")
    return {
        "status": "available",
        "environment_id": environment_id,
        "benchmark_contract": "door-key-public-readback-gap",
        "seed": float(result["seed"]),
        "sample_count_requested": float(result["sample_count_requested"]),
        "sample_count_collected": float(result["sample_count_collected"]),
        "observation_key": "image",
        "observation_shape_contract": [7.0, 7.0, 3.0],
        "action_space_contract": "Discrete",
        "dependency_status": {
            "gymnasium": "external-executed",
            "minigrid": "external-executed",
        },
        "metrics": {
            "distinction_accuracy": float(result["distinction_accuracy"]),
            "gap_detection_auc": float(result["gap_detection_auc"]),
            "unlogged_error_rate": float(result["unlogged_error_rate"]),
            "certified_coverage": float(result["certified_coverage"]),
            "bedc_debt_score": float(result["bedc_debt_score"]),
        },
        "cannot_claim": [],
    }


def import_public_minigrid_benchmark_metrics_file(source: str | Path, target: str | Path) -> dict[str, Any]:
    result = json.loads(Path(source).read_text(encoding="utf-8"))
    packet = import_public_minigrid_benchmark_metrics(result)
    target_path = Path(target)
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def write_public_minigrid_benchmark_packet(path: str | Path) -> dict[str, Any]:
    packet = build_public_minigrid_benchmark_packet()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet
