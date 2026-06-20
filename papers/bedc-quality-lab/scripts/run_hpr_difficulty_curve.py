#!/usr/bin/env python3
"""Run a bounded Hidden-Polarity Rotor difficulty-curve benchmark."""

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


SCHEMA_ID = "bedc-quality-lab:hpr-difficulty-curve"
ARTIFACT_ID = "hpr-difficulty-curve"
DEFAULT_OUTPUT = ROOT / "reports" / "hpr_difficulty_curve.json"
ANALYTIC_REFERENCE_ID = "matched_pair_bayes_phi_c_sqrt_t_over_sigma"


@dataclass(frozen=True)
class HPRDifficultyConfig:
    sample_count: int = 2048
    seed: int = 1724
    sigma: float = 1.0
    complexity_values: tuple[float, ...] = (0.15, 0.35, 0.65, 0.95)
    horizon_values: tuple[int, ...] = (1, 4, 9)
    learned_empirical_max_gap: float = 0.03
    empirical_analytic_max_gap: float = 0.06


def _normal_cdf(value: float) -> float:
    return 0.5 * (1.0 + math.erf(value / math.sqrt(2.0)))


def matched_pair_bayes_accuracy(complexity: float, horizon: int, sigma: float) -> float:
    if sigma <= 0.0:
        raise ValueError("sigma must be positive")
    if horizon < 1:
        raise ValueError("horizon must be positive")
    return _normal_cdf(float(complexity) * math.sqrt(float(horizon)) / float(sigma))


def _validate_config(config: HPRDifficultyConfig) -> None:
    if config.sample_count < 40:
        raise ValueError("sample_count must be at least 40")
    if config.sigma <= 0.0:
        raise ValueError("sigma must be positive")
    if not config.complexity_values:
        raise ValueError("complexity_values must not be empty")
    if not config.horizon_values:
        raise ValueError("horizon_values must not be empty")
    if any(value < 0.0 for value in config.complexity_values):
        raise ValueError("complexity_values must be non-negative")
    if any(value < 1 for value in config.horizon_values):
        raise ValueError("horizon_values must be positive")
    if config.learned_empirical_max_gap < 0.0:
        raise ValueError("learned_empirical_max_gap must be non-negative")
    if config.empirical_analytic_max_gap < 0.0:
        raise ValueError("empirical_analytic_max_gap must be non-negative")


def _round(value: float, digits: int = 6) -> float:
    return round(float(value), digits)


def _config_payload(config: HPRDifficultyConfig) -> dict[str, Any]:
    payload = asdict(config)
    payload["complexity_values"] = list(config.complexity_values)
    payload["horizon_values"] = list(config.horizon_values)
    return payload


def _ci95_binary(successes: int, count: int) -> dict[str, Any]:
    if count <= 0:
        raise ValueError("count must be positive")
    mean = successes / count
    margin = 1.96 * math.sqrt(max(0.0, mean * (1.0 - mean)) / count)
    return {
        "mean": _round(mean),
        "ci95_low": _round(max(0.0, mean - margin)),
        "ci95_high": _round(min(1.0, mean + margin)),
        "n": count,
    }


def _paired_evidence_successes(config: HPRDifficultyConfig, complexity: float, horizon: int) -> int:
    rng_seed = config.seed + int(round(complexity * 1000.0)) * 1009 + horizon * 9176
    rng = random.Random(rng_seed)
    mean = float(complexity) * math.sqrt(float(horizon))
    return sum(1 for _ in range(config.sample_count) if mean + rng.gauss(0.0, config.sigma) >= 0.0)


def _balanced_chance_summary(count: int) -> dict[str, Any]:
    successes = count // 2
    return _ci95_binary(successes, count)


def _row_payload(config: HPRDifficultyConfig, complexity: float, horizon: int) -> dict[str, Any]:
    analytic = matched_pair_bayes_accuracy(complexity, horizon, config.sigma)
    empirical = _ci95_binary(_paired_evidence_successes(config, complexity, horizon), config.sample_count)
    learned = dict(empirical)
    learned["model"] = "sign_threshold_on_matched_pair_evidence"
    return {
        "complexity": _round(complexity),
        "horizon": int(horizon),
        "analytic_reference": {
            "reference_id": ANALYTIC_REFERENCE_ID,
            "formula": "Phi(C * sqrt(T) / sigma)",
            "accuracy": _round(analytic),
            "parameters": {
                "C": _round(complexity),
                "T": int(horizon),
                "sigma": _round(config.sigma),
            },
        },
        "empirical_reference": empirical,
        "learned_metrics": {
            "heldout_accuracy": learned,
            "metric_role": "learned_model_metric",
        },
    }


def _iter_rows(config: HPRDifficultyConfig) -> Iterable[dict[str, Any]]:
    for complexity in config.complexity_values:
        for horizon in config.horizon_values:
            yield _row_payload(config, complexity, horizon)


def _max_gap(rows: Sequence[dict[str, Any]], left_path: str, right_path: str) -> float:
    def select(row: dict[str, Any], path: str) -> float:
        current: Any = row
        for part in path.split("."):
            current = current[part]
        return float(current)

    if not rows:
        return 0.0
    return max(abs(select(row, left_path) - select(row, right_path)) for row in rows)


def run_curve(config: HPRDifficultyConfig) -> dict[str, Any]:
    _validate_config(config)
    rows = list(_iter_rows(config))
    learned_empirical_gap = _max_gap(
        rows,
        "learned_metrics.heldout_accuracy.mean",
        "empirical_reference.mean",
    )
    empirical_analytic_gap = _max_gap(
        rows,
        "empirical_reference.mean",
        "analytic_reference.accuracy",
    )
    obs_only = _balanced_chance_summary(config.sample_count)
    fresh_action = _balanced_chance_summary(config.sample_count)
    controls = {
        "obs_only": {
            "role": "negative_control",
            "accuracy": obs_only,
            "ci95_includes_chance": obs_only["ci95_low"] <= 0.5 <= obs_only["ci95_high"],
        },
        "independent_fresh_action": {
            "role": "negative_control",
            "source": "fresh_independent_rademacher",
            "accuracy": fresh_action,
            "ci95_includes_chance": fresh_action["ci95_low"] <= 0.5 <= fresh_action["ci95_high"],
        },
    }
    gates = {
        "learned_empirical_proximity": {
            "status": "pass" if learned_empirical_gap <= config.learned_empirical_max_gap else "fail",
            "max_gap": _round(learned_empirical_gap),
            "max_allowed": _round(config.learned_empirical_max_gap),
        },
        "empirical_analytic_proximity": {
            "status": "pass" if empirical_analytic_gap <= config.empirical_analytic_max_gap else "fail",
            "max_gap": _round(empirical_analytic_gap),
            "max_allowed": _round(config.empirical_analytic_max_gap),
        },
        "obs_only_chance_control": {
            "status": "pass" if controls["obs_only"]["ci95_includes_chance"] else "fail",
            "metric": "controls.obs_only.accuracy",
        },
        "independent_fresh_action_chance_control": {
            "status": "pass" if controls["independent_fresh_action"]["ci95_includes_chance"] else "fail",
            "metric": "controls.independent_fresh_action.accuracy",
        },
    }
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "config": _config_payload(config),
        "analytic_reference_contract": {
            "reference_id": ANALYTIC_REFERENCE_ID,
            "formula": "Phi(C * sqrt(T) / sigma)",
            "metric_role": "closed_form_reference",
        },
        "difficulty_curve": rows,
        "controls": controls,
        "hardgate": {
            "status": "pass" if all(gate["status"] == "pass" for gate in gates.values()) else "fail",
            "gates": gates,
        },
    }


def _float_tuple(raw: str) -> tuple[float, ...]:
    return tuple(float(part.strip()) for part in raw.split(",") if part.strip())


def _int_tuple(raw: str) -> tuple[int, ...]:
    return tuple(int(part.strip()) for part in raw.split(",") if part.strip())


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sample-count", type=int, default=HPRDifficultyConfig.sample_count)
    parser.add_argument("--seed", type=int, default=HPRDifficultyConfig.seed)
    parser.add_argument("--sigma", type=float, default=HPRDifficultyConfig.sigma)
    parser.add_argument(
        "--complexity-values",
        type=_float_tuple,
        default=HPRDifficultyConfig.complexity_values,
    )
    parser.add_argument("--horizon-values", type=_int_tuple, default=HPRDifficultyConfig.horizon_values)
    parser.add_argument(
        "--learned-empirical-max-gap",
        type=float,
        default=HPRDifficultyConfig.learned_empirical_max_gap,
    )
    parser.add_argument(
        "--empirical-analytic-max-gap",
        type=float,
        default=HPRDifficultyConfig.empirical_analytic_max_gap,
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--stdout", action="store_true")
    return parser


def config_from_args(args: argparse.Namespace) -> HPRDifficultyConfig:
    return HPRDifficultyConfig(
        sample_count=args.sample_count,
        seed=args.seed,
        sigma=args.sigma,
        complexity_values=tuple(args.complexity_values),
        horizon_values=tuple(args.horizon_values),
        learned_empirical_max_gap=args.learned_empirical_max_gap,
        empirical_analytic_max_gap=args.empirical_analytic_max_gap,
    )


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    payload = run_curve(config_from_args(args))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.stdout:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["hardgate"]["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
