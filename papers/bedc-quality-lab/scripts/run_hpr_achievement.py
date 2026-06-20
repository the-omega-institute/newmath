#!/usr/bin/env python3
"""Run the Hidden-Polarity Rotor achievement benchmark."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
import random
import sys
from pathlib import Path
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


SCHEMA_ID = "bedc-quality-lab:hpr-achievement-benchmark"
ARTIFACT_ID = "hpr-achievement"
DEFAULT_OUTPUT = ROOT / "reports" / "hpr_achievement.json"


@dataclass(frozen=True)
class HPRAchievementConfig:
    sample_count: int = 512
    seed: int = 1717
    train_fraction: float = 0.5
    observation_noise: float = 0.15
    min_endpoint_accuracy: float = 0.9
    max_fake_action_accuracy: float = 0.62


@dataclass(frozen=True)
class HPRSample:
    observation: float
    action: int
    fake_action: int
    action_shuffled_diagnostic: int
    endpoint: int


def _rademacher(rng: random.Random) -> int:
    return -1 if rng.random() < 0.5 else 1


def _validate_config(config: HPRAchievementConfig) -> None:
    if config.sample_count < 20:
        raise ValueError("sample_count must be at least 20")
    if not 0.1 <= config.train_fraction <= 0.9:
        raise ValueError("train_fraction must be between 0.1 and 0.9")
    if config.observation_noise < 0:
        raise ValueError("observation_noise must be non-negative")
    if not 0.0 <= config.min_endpoint_accuracy <= 1.0:
        raise ValueError("min_endpoint_accuracy must be between 0 and 1")
    if not 0.0 <= config.max_fake_action_accuracy <= 1.0:
        raise ValueError("max_fake_action_accuracy must be between 0 and 1")


def _generate_samples(config: HPRAchievementConfig) -> list[HPRSample]:
    rng = random.Random(config.seed)
    fake_rng = random.Random(config.seed + 104729)
    polarities: list[int] = []
    observations: list[float] = []
    actions: list[int] = []
    fake_actions: list[int] = []

    for _ in range(config.sample_count):
        polarity = _rademacher(rng)
        action = _rademacher(rng)
        noise = rng.uniform(-config.observation_noise, config.observation_noise)
        polarities.append(polarity)
        observations.append(float(polarity + noise))
        actions.append(action)
        fake_actions.append(_rademacher(fake_rng))

    shuffled_actions = actions[1:] + actions[:1]
    return [
        HPRSample(
            observation=observations[index],
            action=actions[index],
            fake_action=fake_actions[index],
            action_shuffled_diagnostic=shuffled_actions[index],
            endpoint=1 if polarities[index] * actions[index] > 0 else 0,
        )
        for index in range(config.sample_count)
    ]


def _score(sample: HPRSample, action_attr: str) -> float:
    return float(sample.observation * int(getattr(sample, action_attr)))


def _best_threshold(samples: Sequence[HPRSample], action_attr: str) -> float:
    scores = sorted({_score(sample, action_attr) for sample in samples})
    if len(scores) == 1:
        return scores[0]
    candidates = [scores[0] - 1.0]
    candidates.extend((left + right) / 2.0 for left, right in zip(scores, scores[1:]))
    candidates.append(scores[-1] + 1.0)
    return max(candidates, key=lambda threshold: _accuracy(samples, action_attr, threshold))


def _accuracy(samples: Sequence[HPRSample], action_attr: str, threshold: float) -> float:
    if not samples:
        return 0.0
    correct = 0
    for sample in samples:
        prediction = 1 if _score(sample, action_attr) >= threshold else 0
        if prediction == sample.endpoint:
            correct += 1
    return correct / len(samples)


def _obs_only_accuracy(samples: Sequence[HPRSample]) -> float:
    if not samples:
        return 0.0
    positives = sum(sample.endpoint for sample in samples)
    majority = 1 if positives >= len(samples) / 2 else 0
    correct = sum(1 for sample in samples if sample.endpoint == majority)
    return correct / len(samples)


def _mean(values: Iterable[int]) -> float:
    materialized = list(values)
    return float(sum(materialized) / len(materialized)) if materialized else 0.0


def run_benchmark(config: HPRAchievementConfig) -> dict[str, Any]:
    _validate_config(config)
    samples = _generate_samples(config)
    split_index = max(1, min(len(samples) - 1, int(round(len(samples) * config.train_fraction))))
    train_samples = samples[:split_index]
    test_samples = samples[split_index:]
    threshold = _best_threshold(train_samples, "action")

    endpoint_accuracy = _accuracy(test_samples, "action", threshold)
    fake_action_accuracy = _accuracy(test_samples, "fake_action", threshold)
    shuffled_accuracy = _accuracy(test_samples, "action_shuffled_diagnostic", threshold)
    obs_only_accuracy = _obs_only_accuracy(test_samples)
    fake_action_rate = _mean(sample.fake_action for sample in samples)
    action_rate = _mean(sample.action for sample in samples)

    endpoint_gate = endpoint_accuracy >= config.min_endpoint_accuracy
    fake_action_gate = fake_action_accuracy <= config.max_fake_action_accuracy
    status = "pass" if endpoint_gate and fake_action_gate else "fail"

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "config": asdict(config),
        "sample_summary": {
            "train_count": len(train_samples),
            "test_count": len(test_samples),
            "action_mean": round(action_rate, 6),
            "fake_action_mean": round(fake_action_rate, 6),
            "fake_action_source": "fresh_independent_rademacher",
        },
        "model": {
            "classifier": "threshold_on_observation_times_action",
            "threshold": round(float(threshold), 12),
        },
        "metrics": {
            "endpoint_accuracy": round(endpoint_accuracy, 6),
            "obs_only_control_accuracy": round(obs_only_accuracy, 6),
            "fake_action_control_accuracy": round(fake_action_accuracy, 6),
            "action_shuffled_diagnostic_accuracy": round(shuffled_accuracy, 6),
        },
        "controls": {
            "fake_action": {
                "role": "negative_control",
                "source": "fresh_independent_rademacher",
                "metric": "fake_action_control_accuracy",
                "max_allowed": config.max_fake_action_accuracy,
                "status": "pass" if fake_action_gate else "fail",
            },
            "action_shuffled_diagnostic": {
                "role": "report_only_diagnostic",
                "source": "same_trajectory_cyclic_action_shuffle",
                "metric": "action_shuffled_diagnostic_accuracy",
                "status": "reported",
            },
            "obs_only": {
                "role": "control",
                "metric": "obs_only_control_accuracy",
                "status": "reported",
            },
        },
        "hardgate": {
            "status": status,
            "gates": {
                "endpoint": {
                    "status": "pass" if endpoint_gate else "fail",
                    "metric": "endpoint_accuracy",
                    "min_allowed": config.min_endpoint_accuracy,
                },
                "fake_action": {
                    "status": "pass" if fake_action_gate else "fail",
                    "metric": "fake_action_control_accuracy",
                    "max_allowed": config.max_fake_action_accuracy,
                },
            },
            "excluded_from_hardgate": ["action_shuffled_diagnostic", "obs_only"],
        },
    }


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sample-count", type=int, default=HPRAchievementConfig.sample_count)
    parser.add_argument("--seed", type=int, default=HPRAchievementConfig.seed)
    parser.add_argument("--train-fraction", type=float, default=HPRAchievementConfig.train_fraction)
    parser.add_argument("--observation-noise", type=float, default=HPRAchievementConfig.observation_noise)
    parser.add_argument("--min-endpoint-accuracy", type=float, default=HPRAchievementConfig.min_endpoint_accuracy)
    parser.add_argument("--max-fake-action-accuracy", type=float, default=HPRAchievementConfig.max_fake_action_accuracy)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--stdout", action="store_true", help="Also print the JSON payload to stdout.")
    return parser.parse_args(argv)


def config_from_args(args: argparse.Namespace) -> HPRAchievementConfig:
    return HPRAchievementConfig(
        sample_count=args.sample_count,
        seed=args.seed,
        train_fraction=args.train_fraction,
        observation_noise=args.observation_noise,
        min_endpoint_accuracy=args.min_endpoint_accuracy,
        max_fake_action_accuracy=args.max_fake_action_accuracy,
    )


def main(argv: Sequence[str] | None = None) -> dict[str, Any]:
    args = parse_args(argv)
    payload = run_benchmark(config_from_args(args))
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    if args.stdout:
        print(rendered, end="")
    return payload


if __name__ == "__main__":
    main()
