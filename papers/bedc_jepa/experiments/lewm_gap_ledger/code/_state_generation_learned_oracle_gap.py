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
DEFAULT_PRED = REPORT_DIR / "state_generation_residual_benefit_selector_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_learned_oracle_gap.json"
DEFAULT_MD = REPORT_DIR / "state_generation_learned_oracle_gap.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"


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


def summarize_score(
    split: dict[str, np.ndarray],
    score: np.ndarray,
    oracle_score: np.ndarray,
    hard_mask: np.ndarray,
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for budget_index, multiplier in enumerate((2, 3, 4)):
        oracle_eps, oracle_values = episode_values(split, oracle_score, hard_mask, multiplier)
        score_eps, score_values = episode_values(split, score, hard_mask, multiplier)
        if oracle_eps != score_eps:
            raise ValueError(f"episode order mismatch for budget {multiplier}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values)) if len(oracle_values) else 0.0
        score_mean = float(np.mean(score_values)) if len(score_values) else 0.0
        captured = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        out[f"budget_{multiplier}"] = {
            "score_delta": bootstrap_mean(score_values, seed=seed + 1009 * budget_index, samples=samples),
            "oracle_delta": bootstrap_mean(oracle_values, seed=seed + 1009 * budget_index + 17, samples=samples),
            "regret_to_oracle": bootstrap_mean(regret, seed=seed + 1009 * budget_index + 31, samples=samples),
            "headroom_capture_ratio": clean_float(float(captured)),
            "missed_headroom_ratio": clean_float(float(1.0 - captured)),
            "episode_count": int(len(score_values)),
        }
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Learned Oracle Gap",
        "",
        "| scorer | budget | score delta | oracle delta | regret | capture |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for scorer in ["benefit_selector", "priority_residual", "raw_geometry_option"]:
        for budget in ["budget_2", "budget_3", "budget_4"]:
            row = report["rows"][scorer][budget]
            lines.append(
                f"| `{scorer}` | `{budget}` | {row['score_delta']['observed']:.6g} | "
                f"{row['oracle_delta']['observed']:.6g} | {row['regret_to_oracle']['observed']:.6g} | "
                f"{row['headroom_capture_ratio']:.6g} |"
            )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Decompose learned hard-budget allocation scores against the oracle ceiling")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--predictions", default=str(DEFAULT_PRED))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=977)
    parser.add_argument("--bootstrap-samples", type=int, default=4000)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    pred = load_npz(Path(args.predictions))
    eval_split = episode_alloc.load_split(data, "eval")
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    oracle_score = eval_split["option_error"].astype(np.float64)
    scores = {
        "benefit_selector": pred["benefit_selector_score"].astype(np.float64),
        "priority_residual": pred["priority_residual_score"].astype(np.float64),
        "raw_geometry_option": pred["raw_geometry_option_score"].astype(np.float64),
    }
    rows = {
        name: summarize_score(
            eval_split,
            score,
            oracle_score,
            hard_mask,
            seed=int(args.seed) + index * 10000,
            samples=int(args.bootstrap_samples),
        )
        for index, (name, score) in enumerate(scores.items())
    }
    best_budget3_capture = max(float(rows[name]["budget_3"]["headroom_capture_ratio"]) for name in rows)
    worst_budget4_capture = min(float(rows[name]["budget_4"]["headroom_capture_ratio"]) for name in rows)
    best_budget3_regret = min(float(rows[name]["budget_3"]["regret_to_oracle"]["observed"]) for name in rows)
    closes_gap = best_budget3_capture >= 0.5 and worst_budget4_capture > 0.0
    if closes_gap:
        verdict = (
            "At least one learned score captures a large share of the hard budget-3 oracle headroom without reversing "
            "at budget four; the learned-oracle gap is narrowed but still must pass direct allocation closure."
        )
    else:
        verdict = (
            "The learned scores remain far from the hard exact-budget oracle ceiling: budget-3 captures only a small "
            "fraction of oracle headroom and budget-four capture can reverse sign. The missing object is a learned "
            "option-conditioned compute-value score, not another scalar failure-rank transform."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_learned_oracle_gap",
        "config": {
            "seed": int(args.seed),
            "bootstrap_samples": int(args.bootstrap_samples),
            "budget_multipliers": [2, 3, 4],
            "learned_score_source": str(Path(args.predictions)),
            "oracle_scope": "eval option_error ceiling only",
        },
        "hard_episode_union": hard_episodes,
        "rows": rows,
        "diagnosis": {
            "learned_oracle_gap_closes": bool(closes_gap),
            "best_budget3_capture_ratio": clean_float(float(best_budget3_capture)),
            "best_budget3_regret": clean_float(float(best_budget3_regret)),
            "worst_budget4_capture_ratio": clean_float(float(worst_budget4_capture)),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "learned_scores": "fixed eval scores are consumed without retraining",
            "oracle_scope": "eval option_error is used only after fixed score generation to measure oracle headroom and regret",
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
