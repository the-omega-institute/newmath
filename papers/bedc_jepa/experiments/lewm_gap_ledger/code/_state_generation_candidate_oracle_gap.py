from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_candidate_oracle_gap.json"
DEFAULT_MD = REPORT_DIR / "state_generation_candidate_oracle_gap.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"


CANDIDATE_SOURCES = {
    "episode_assignment_value": ("state_generation_episode_assignment_value_predictions.npz", "episode_assignment_value_score"),
    "assignment_priority_residual": ("state_generation_episode_assignment_value_predictions.npz", "priority_residual_score"),
    "assignment_raw_geometry": ("state_generation_episode_assignment_value_predictions.npz", "raw_geometry_option_score"),
    "episode_regret": ("state_generation_episode_regret_predictions.npz", "episode_regret_score"),
    "regret_episode_allocation": ("state_generation_episode_regret_predictions.npz", "episode_allocation_score"),
    "regret_dual_price": ("state_generation_episode_regret_predictions.npz", "dual_price_score"),
    "regret_allocation_native": ("state_generation_episode_regret_predictions.npz", "allocation_native_score"),
    "episode_allocation": ("state_generation_episode_allocation_predictions.npz", "episode_allocation_score"),
    "episode_seed_mean": ("state_generation_episode_seed_ensemble_predictions.npz", "mean_score"),
    "episode_seed_median": ("state_generation_episode_seed_ensemble_predictions.npz", "median_score"),
    "episode_balanced": ("state_generation_episode_balanced_predictions.npz", "episode_balanced_score"),
    "episode_dual_price": ("state_generation_episode_dual_price_predictions.npz", "dual_price_score"),
    "benefit_selector": ("state_generation_residual_benefit_selector_predictions.npz", "benefit_selector_score"),
    "residual_priority": ("state_generation_residual_benefit_selector_predictions.npz", "priority_residual_score"),
    "residual_raw": ("state_generation_residual_benefit_selector_predictions.npz", "raw_geometry_option_score"),
    "budget_priority": ("state_generation_budget_priority_residual_predictions.npz", "priority_residual_score"),
    "budget_raw": ("state_generation_budget_priority_residual_predictions.npz", "raw_geometry_option_score"),
    "geometry_option_conditioned": ("state_generation_geometry_option_conditioned_allocation_predictions.npz", "geometry_option_conditioned_score"),
    "geometry_conditioned": ("state_generation_geometry_option_conditioned_allocation_predictions.npz", "geometry_conditioned_score"),
    "geometry_regime_weighted": ("state_generation_geometry_option_conditioned_allocation_predictions.npz", "geometry_regime_weighted_score"),
    "allocation_native": ("state_generation_allocation_native_predictions.npz", "allocation_native_score"),
    "calibrated_allocation_native": ("state_generation_allocation_native_predictions.npz", "calibrated_allocation_native_score"),
}


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating,)):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def bootstrap_mean(values: np.ndarray, *, seed: int, samples: int) -> dict[str, Any]:
    values = values.astype(np.float64)
    if len(values) == 0:
        return {"observed": 0.0, "low": 0.0, "high": 0.0, "samples": 0, "episode_count": 0}
    rng = np.random.default_rng(int(seed))
    boot = np.zeros(int(samples), dtype=np.float64)
    for index in range(int(samples)):
        idx = rng.integers(0, len(values), size=len(values))
        boot[index] = float(np.mean(values[idx]))
    return {
        "observed": clean_float(float(np.mean(values))),
        "low": clean_float(float(np.quantile(boot, 0.025))),
        "high": clean_float(float(np.quantile(boot, 0.975))),
        "samples": int(samples),
        "episode_count": int(len(values)),
    }


def episode_values(
    split: dict[str, np.ndarray],
    score: np.ndarray,
    mask: np.ndarray,
    multiplier: int,
) -> tuple[list[int], np.ndarray]:
    rows = budget_audit.episode_rows(split, score.astype(np.float64), mask.astype(bool), int(multiplier))
    return [int(row["episode"]) for row in rows], np.asarray([float(row["selected_minus_uniform"]) for row in rows], dtype=np.float64)


def load_candidates(eval_split: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    out: dict[str, np.ndarray] = {}
    for name, (filename, key) in CANDIDATE_SOURCES.items():
        path = REPORT_DIR / filename
        if not path.exists():
            continue
        data = load_npz(path)
        if key not in data:
            continue
        score = data[key].astype(np.float64)
        if score.shape != eval_split["option_error"].shape:
            continue
        out[name] = score
    return out


def summarize_candidate(
    split: dict[str, np.ndarray],
    score: np.ndarray,
    oracle_score: np.ndarray,
    hard_mask: np.ndarray,
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    for budget_index, multiplier in enumerate((2, 3, 4)):
        oracle_eps, oracle_values = episode_values(split, oracle_score, hard_mask, multiplier)
        score_eps, score_values = episode_values(split, score, hard_mask, multiplier)
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {multiplier}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{multiplier}"] = {
            "score_delta": bootstrap_mean(score_values, seed=seed + 1009 * budget_index, samples=samples),
            "oracle_delta": bootstrap_mean(oracle_values, seed=seed + 1009 * budget_index + 17, samples=samples),
            "regret_to_oracle": bootstrap_mean(regret, seed=seed + 1009 * budget_index + 31, samples=samples),
            "headroom_capture_ratio": clean_float(float(capture)),
        }
    return {
        "budgets": budgets,
        "summary": {
            "mean_capture_ratio": clean_float(float(np.mean(captures))),
            "min_capture_ratio": clean_float(float(np.min(captures))),
            "max_capture_ratio": clean_float(float(np.max(captures))),
            "mean_regret_to_oracle": clean_float(float(np.mean(regrets))),
            "budget3_capture_ratio": clean_float(float(captures[1])),
            "budget4_capture_ratio": clean_float(float(captures[2])),
        },
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Candidate Oracle Gap",
        "",
        f"- candidate count: `{report['candidate_count']}`",
        f"- best candidate: `{report['diagnosis']['best_candidate']}`",
        "",
        "| candidate | mean capture | budget-3 capture | budget-4 capture | mean regret |",
        "|---|---:|---:|---:|---:|",
    ]
    for row in report["ranking"][:12]:
        lines.append(
            f"| `{row['candidate']}` | {row['mean_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | "
            f"{row['mean_regret_to_oracle']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit existing learned candidate scores against the hard oracle budget ceiling")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=991)
    parser.add_argument("--bootstrap-samples", type=int, default=4000)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    eval_split = episode_alloc.load_split(data, "eval")
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    oracle_score = eval_split["option_error"].astype(np.float64)
    candidates = load_candidates(eval_split)
    rows = {
        name: summarize_candidate(
            eval_split,
            score,
            oracle_score,
            hard_mask,
            seed=int(args.seed) + index * 10000,
            samples=int(args.bootstrap_samples),
        )
        for index, (name, score) in enumerate(sorted(candidates.items()))
    }
    ranking = [
        {
            "candidate": name,
            **payload["summary"],
        }
        for name, payload in rows.items()
    ]
    ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    best = ranking[0] if ranking else {
        "candidate": "",
        "mean_capture_ratio": 0.0,
        "budget3_capture_ratio": 0.0,
        "budget4_capture_ratio": 0.0,
        "mean_regret_to_oracle": 0.0,
    }
    candidate_pool_closes = bool(float(best["mean_capture_ratio"]) >= 0.5 and float(best["budget4_capture_ratio"]) > 0.0)
    if candidate_pool_closes:
        verdict = (
            "An existing learned candidate captures a substantial share of hard oracle headroom across budget stress; "
            "direct allocation closure and independent export validation remain required."
        )
    else:
        verdict = (
            "No existing learned candidate approaches the hard oracle budget ceiling. The candidate pool audit supports "
            "a new option-conditioned compute-value objective rather than more selection over existing score families."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_candidate_oracle_gap",
        "config": {
            "seed": int(args.seed),
            "bootstrap_samples": int(args.bootstrap_samples),
            "budget_multipliers": [2, 3, 4],
            "candidate_sources": CANDIDATE_SOURCES,
        },
        "candidate_count": int(len(candidates)),
        "hard_episode_union": hard_episodes,
        "rows": rows,
        "ranking": ranking,
        "diagnosis": {
            "candidate_pool_closes": candidate_pool_closes,
            "best_candidate": str(best["candidate"]),
            "best_mean_capture_ratio": clean_float(float(best["mean_capture_ratio"])),
            "best_budget3_capture_ratio": clean_float(float(best["budget3_capture_ratio"])),
            "best_budget4_capture_ratio": clean_float(float(best["budget4_capture_ratio"])),
            "best_mean_regret_to_oracle": clean_float(float(best["mean_regret_to_oracle"])),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "learned_scores": "fixed eval score artifacts are consumed without retraining",
            "oracle_scope": "eval option_error is used only after fixed score generation to measure ceiling regret and capture",
            "hard_ids": "held-out hard episode ids are used only for diagnostic slicing",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": [
            "deployable allocation policy",
            "learned compute-value closure",
            "independent export validation",
            "complete BEDC-native world model",
        ],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).write_text(
        json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
