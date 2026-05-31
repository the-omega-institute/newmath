"""Optional adapter for public MiniGrid-family environments."""

from __future__ import annotations

from dataclasses import dataclass, asdict
import importlib.util
import json
from pathlib import Path
from typing import Any

import numpy as np


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
