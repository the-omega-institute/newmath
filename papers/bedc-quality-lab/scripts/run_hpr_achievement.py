#!/usr/bin/env python3
"""Run the Hidden-Polarity Rotor achievement benchmark."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
import math
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
ARM_ENDPOINT = "endpoint"
ARM_FAKE_ACTION = "fake_action"
ARM_ACTION_SHUFFLED = "action_shuffled_diagnostic"
ARM_OBS_ONLY = "obs_only"
REPORT_ONLY_ARMS = [ARM_ACTION_SHUFFLED, ARM_OBS_ONLY]


@dataclass(frozen=True)
class HPRAchievementConfig:
    sample_count: int = 512
    seed: int = 1717
    seed_count: int = 9
    train_fraction: float = 0.5
    observation_noise: float = 0.15
    logistic_epochs: int = 240
    learning_rate: float = 0.8
    l2_penalty: float = 0.001
    min_endpoint_auc: float = 0.95
    max_fake_action_auc: float = 0.62
    min_endpoint_fake_auc_gap_ci_low: float = 0.25


@dataclass(frozen=True)
class HPRSample:
    observation: float
    action: int
    fake_action: int
    action_shuffled_diagnostic: int
    endpoint: int


@dataclass(frozen=True)
class LearnedArmResult:
    heldout_auc: float
    heldout_accuracy: float
    weights: list[float]


def _rademacher(rng: random.Random) -> int:
    return -1 if rng.random() < 0.5 else 1


def _validate_config(config: HPRAchievementConfig) -> None:
    if config.sample_count < 40:
        raise ValueError("sample_count must be at least 40")
    if config.seed_count < 2:
        raise ValueError("seed_count must be at least 2")
    if not 0.1 <= config.train_fraction <= 0.9:
        raise ValueError("train_fraction must be between 0.1 and 0.9")
    if config.observation_noise < 0:
        raise ValueError("observation_noise must be non-negative")
    if config.logistic_epochs < 1:
        raise ValueError("logistic_epochs must be positive")
    if config.learning_rate <= 0:
        raise ValueError("learning_rate must be positive")
    if config.l2_penalty < 0:
        raise ValueError("l2_penalty must be non-negative")
    if not 0.0 <= config.min_endpoint_auc <= 1.0:
        raise ValueError("min_endpoint_auc must be between 0 and 1")
    if not 0.0 <= config.max_fake_action_auc <= 1.0:
        raise ValueError("max_fake_action_auc must be between 0 and 1")
    if not 0.0 <= config.min_endpoint_fake_auc_gap_ci_low <= 1.0:
        raise ValueError("min_endpoint_fake_auc_gap_ci_low must be between 0 and 1")


def _generate_samples(config: HPRAchievementConfig, seed: int) -> list[HPRSample]:
    rng = random.Random(seed)
    fake_rng = random.Random(seed + 104729)
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


def _split_samples(config: HPRAchievementConfig, samples: Sequence[HPRSample]) -> tuple[list[HPRSample], list[HPRSample]]:
    split_index = max(1, min(len(samples) - 1, int(round(len(samples) * config.train_fraction))))
    return list(samples[:split_index]), list(samples[split_index:])


def _features(sample: HPRSample, arm: str) -> list[float]:
    if arm == ARM_OBS_ONLY:
        return [1.0, sample.observation]
    action_value = sample.action if arm == ARM_ENDPOINT else int(getattr(sample, arm))
    return [1.0, sample.observation, float(action_value), sample.observation * action_value]


def _sigmoid(value: float) -> float:
    if value >= 0:
        z = math.exp(-value)
        return 1.0 / (1.0 + z)
    z = math.exp(value)
    return z / (1.0 + z)


def _dot(left: Sequence[float], right: Sequence[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def _fit_logistic(samples: Sequence[HPRSample], arm: str, config: HPRAchievementConfig) -> list[float]:
    if not samples:
        return []
    weights = [0.0 for _ in _features(samples[0], arm)]
    scale = 1.0 / len(samples)
    for _ in range(config.logistic_epochs):
        gradient = [0.0 for _ in weights]
        for sample in samples:
            row = _features(sample, arm)
            error = _sigmoid(_dot(weights, row)) - sample.endpoint
            for index, value in enumerate(row):
                gradient[index] += error * value
        for index in range(len(weights)):
            regularizer = 0.0 if index == 0 else config.l2_penalty * weights[index]
            weights[index] -= config.learning_rate * ((gradient[index] * scale) + regularizer)
    return weights


def _scores(samples: Sequence[HPRSample], weights: Sequence[float], arm: str) -> list[float]:
    return [_dot(weights, _features(sample, arm)) for sample in samples]


def _auc(labels: Sequence[int], scores: Sequence[float]) -> float:
    positives = [score for label, score in zip(labels, scores) if label == 1]
    negatives = [score for label, score in zip(labels, scores) if label == 0]
    if not positives or not negatives:
        return 0.5
    wins = 0.0
    for positive in positives:
        for negative in negatives:
            if positive > negative:
                wins += 1.0
            elif positive == negative:
                wins += 0.5
    return wins / (len(positives) * len(negatives))


def _accuracy(labels: Sequence[int], scores: Sequence[float]) -> float:
    if not labels:
        return 0.0
    correct = sum(1 for label, score in zip(labels, scores) if (1 if score >= 0 else 0) == label)
    return correct / len(labels)


def _learn_and_evaluate(
    train_samples: Sequence[HPRSample],
    test_samples: Sequence[HPRSample],
    arm: str,
    config: HPRAchievementConfig,
) -> LearnedArmResult:
    weights = _fit_logistic(train_samples, arm, config)
    labels = [sample.endpoint for sample in test_samples]
    scores = _scores(test_samples, weights, arm)
    return LearnedArmResult(
        heldout_auc=_auc(labels, scores),
        heldout_accuracy=_accuracy(labels, scores),
        weights=weights,
    )


def _mean(values: Iterable[float]) -> float:
    materialized = list(values)
    return float(sum(materialized) / len(materialized)) if materialized else 0.0


def _ci95(values: Sequence[float]) -> dict[str, float]:
    if not values:
        return {"mean": 0.0, "ci95_low": 0.0, "ci95_high": 0.0, "n": 0}
    mean = _mean(values)
    if len(values) == 1:
        margin = 0.0
    else:
        variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
        margin = 1.96 * math.sqrt(variance / len(values))
    return {
        "mean": round(mean, 6),
        "ci95_low": round(max(0.0, mean - margin), 6),
        "ci95_high": round(min(1.0, mean + margin), 6),
        "n": len(values),
    }


def _round_weights(weights: Sequence[float]) -> list[float]:
    return [round(float(weight), 8) for weight in weights]


def _summarize_arm(seed_rows: Sequence[dict[str, Any]], arm: str) -> dict[str, Any]:
    auc_values = [float(row["arms"][arm]["heldout_auc"]) for row in seed_rows]
    accuracy_values = [float(row["arms"][arm]["heldout_accuracy"]) for row in seed_rows]
    return {
        "heldout_auc": _ci95(auc_values),
        "heldout_accuracy": _ci95(accuracy_values),
    }


def _paired_difference(seed_rows: Sequence[dict[str, Any]], left_arm: str, right_arm: str) -> dict[str, Any]:
    differences = [
        float(row["arms"][left_arm]["heldout_auc"]) - float(row["arms"][right_arm]["heldout_auc"])
        for row in seed_rows
    ]
    summary = _ci95(differences)
    summary["left_arm"] = left_arm
    summary["right_arm"] = right_arm
    return summary


def run_benchmark(config: HPRAchievementConfig) -> dict[str, Any]:
    _validate_config(config)
    seed_rows: list[dict[str, Any]] = []

    for offset in range(config.seed_count):
        seed = config.seed + offset
        samples = _generate_samples(config, seed)
        train_samples, test_samples = _split_samples(config, samples)
        arm_results = {
            arm: _learn_and_evaluate(train_samples, test_samples, arm, config)
            for arm in [ARM_ENDPOINT, ARM_FAKE_ACTION, ARM_ACTION_SHUFFLED, ARM_OBS_ONLY]
        }
        seed_rows.append(
            {
                "seed": seed,
                "train_count": len(train_samples),
                "test_count": len(test_samples),
                "arms": {
                    arm: {
                        "heldout_auc": round(result.heldout_auc, 6),
                        "heldout_accuracy": round(result.heldout_accuracy, 6),
                        "weights": _round_weights(result.weights),
                    }
                    for arm, result in arm_results.items()
                },
            }
        )

    arm_summaries = {
        arm: _summarize_arm(seed_rows, arm)
        for arm in [ARM_ENDPOINT, ARM_FAKE_ACTION, ARM_ACTION_SHUFFLED, ARM_OBS_ONLY]
    }
    endpoint_fake_gap = _paired_difference(seed_rows, ARM_ENDPOINT, ARM_FAKE_ACTION)
    endpoint_auc_ci = arm_summaries[ARM_ENDPOINT]["heldout_auc"]
    fake_auc_ci = arm_summaries[ARM_FAKE_ACTION]["heldout_auc"]

    endpoint_gate = endpoint_auc_ci["ci95_low"] >= config.min_endpoint_auc
    fake_action_gate = fake_auc_ci["mean"] <= config.max_fake_action_auc
    paired_gap_gate = endpoint_fake_gap["ci95_low"] >= config.min_endpoint_fake_auc_gap_ci_low
    confound_resistant = endpoint_gate and fake_action_gate and paired_gap_gate

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "config": asdict(config),
        "sample_summary": {
            "seed_count": config.seed_count,
            "sample_count_per_seed": config.sample_count,
            "fake_action_source": "fresh_independent_rademacher",
        },
        "model": {
            "learner": "deterministic_logistic_regression",
            "training_objective": "binary_cross_entropy",
            "heldout_metric": "auc",
            "feature_sets": {
                ARM_ENDPOINT: ["bias", "observation", "action", "observation_x_action"],
                ARM_FAKE_ACTION: ["bias", "observation", "fake_action", "observation_x_fake_action"],
                ARM_ACTION_SHUFFLED: [
                    "bias",
                    "observation",
                    "action_shuffled_diagnostic",
                    "observation_x_action_shuffled_diagnostic",
                ],
                ARM_OBS_ONLY: ["bias", "observation"],
            },
        },
        "metrics": {
            "arms": arm_summaries,
            "paired_differences": {
                "endpoint_minus_fake_action_auc": endpoint_fake_gap,
                "endpoint_minus_obs_only_auc": _paired_difference(seed_rows, ARM_ENDPOINT, ARM_OBS_ONLY),
                "endpoint_minus_action_shuffled_diagnostic_auc": _paired_difference(
                    seed_rows,
                    ARM_ENDPOINT,
                    ARM_ACTION_SHUFFLED,
                ),
            },
            "seed_results": seed_rows,
            "confidence_interval_method": "normal_seed_paired_ci95",
        },
        "controls": {
            ARM_FAKE_ACTION: {
                "role": "negative_control",
                "source": "fresh_independent_rademacher",
                "metric": "$.metrics.arms.fake_action.heldout_auc",
                "max_allowed_mean": config.max_fake_action_auc,
                "status": "pass" if fake_action_gate else "fail",
            },
            ARM_ACTION_SHUFFLED: {
                "role": "report_only_diagnostic",
                "source": "same_trajectory_cyclic_action_shuffle",
                "metric": "$.metrics.arms.action_shuffled_diagnostic.heldout_auc",
                "status": "reported",
            },
            ARM_OBS_ONLY: {
                "role": "report_only_control",
                "metric": "$.metrics.arms.obs_only.heldout_auc",
                "status": "reported",
            },
        },
        "hardgate": {
            "status": "pass" if confound_resistant else "fail",
            "confound_resistant": confound_resistant,
            "gates": {
                "endpoint_heldout_auc": {
                    "status": "pass" if endpoint_gate else "fail",
                    "metric": "$.metrics.arms.endpoint.heldout_auc.ci95_low",
                    "min_allowed": config.min_endpoint_auc,
                    "actual": endpoint_auc_ci["ci95_low"],
                },
                "fake_action_negative_control": {
                    "status": "pass" if fake_action_gate else "fail",
                    "metric": "$.metrics.arms.fake_action.heldout_auc.mean",
                    "max_allowed": config.max_fake_action_auc,
                    "actual": fake_auc_ci["mean"],
                },
                "endpoint_fake_action_auc_gap": {
                    "status": "pass" if paired_gap_gate else "fail",
                    "metric": "$.metrics.paired_differences.endpoint_minus_fake_action_auc.ci95_low",
                    "min_allowed": config.min_endpoint_fake_auc_gap_ci_low,
                    "actual": endpoint_fake_gap["ci95_low"],
                },
            },
            "excluded_from_hardgate": REPORT_ONLY_ARMS,
        },
    }


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sample-count", type=int, default=HPRAchievementConfig.sample_count)
    parser.add_argument("--seed", type=int, default=HPRAchievementConfig.seed)
    parser.add_argument("--seed-count", type=int, default=HPRAchievementConfig.seed_count)
    parser.add_argument("--train-fraction", type=float, default=HPRAchievementConfig.train_fraction)
    parser.add_argument("--observation-noise", type=float, default=HPRAchievementConfig.observation_noise)
    parser.add_argument("--logistic-epochs", type=int, default=HPRAchievementConfig.logistic_epochs)
    parser.add_argument("--learning-rate", type=float, default=HPRAchievementConfig.learning_rate)
    parser.add_argument("--l2-penalty", type=float, default=HPRAchievementConfig.l2_penalty)
    parser.add_argument("--min-endpoint-auc", type=float, default=HPRAchievementConfig.min_endpoint_auc)
    parser.add_argument("--max-fake-action-auc", type=float, default=HPRAchievementConfig.max_fake_action_auc)
    parser.add_argument(
        "--min-endpoint-fake-auc-gap-ci-low",
        type=float,
        default=HPRAchievementConfig.min_endpoint_fake_auc_gap_ci_low,
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--stdout", action="store_true", help="Also print the JSON payload to stdout.")
    return parser.parse_args(argv)


def config_from_args(args: argparse.Namespace) -> HPRAchievementConfig:
    return HPRAchievementConfig(
        sample_count=args.sample_count,
        seed=args.seed,
        seed_count=args.seed_count,
        train_fraction=args.train_fraction,
        observation_noise=args.observation_noise,
        logistic_epochs=args.logistic_epochs,
        learning_rate=args.learning_rate,
        l2_penalty=args.l2_penalty,
        min_endpoint_auc=args.min_endpoint_auc,
        max_fake_action_auc=args.max_fake_action_auc,
        min_endpoint_fake_auc_gap_ci_low=args.min_endpoint_fake_auc_gap_ci_low,
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
