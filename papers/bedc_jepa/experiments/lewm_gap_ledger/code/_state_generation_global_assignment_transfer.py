from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_candidate_oracle_gap as candidate_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_global_assignment_transfer.json"
DEFAULT_MD = REPORT_DIR / "state_generation_global_assignment_transfer.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_global_assignment_transfer_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BUDGETS = np.asarray([2, 3, 4], dtype=np.int64)


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


def candidate_single_scores(eval_shape: tuple[int, int]) -> dict[str, np.ndarray]:
    out: dict[str, np.ndarray] = {}
    for name, (filename, key) in candidate_gap.CANDIDATE_SOURCES.items():
        path = REPORT_DIR / filename
        if not path.exists():
            continue
        data = load_npz(path)
        if key not in data:
            continue
        score = data[key].astype(np.float64)
        if score.shape == eval_shape:
            out[name] = score
    return out


def budget_score_candidates(eval_shape: tuple[int, int]) -> dict[str, dict[int, np.ndarray]]:
    files = [
        "state_generation_budget_replacement_value_predictions.npz",
        "state_generation_budget_conditioned_value_predictions.npz",
        "state_generation_budget_head_value_predictions.npz",
        "state_generation_minimax_budget_policy_predictions.npz",
        "state_generation_episode_coupled_budget_policy_predictions.npz",
    ]
    out: dict[str, dict[int, np.ndarray]] = {}
    for filename in files:
        path = REPORT_DIR / filename
        if not path.exists():
            continue
        data = load_npz(path)
        stem = filename.replace("_predictions.npz", "")
        budget_map: dict[int, np.ndarray] = {}
        for budget in BUDGETS.astype(np.int64):
            preferred = f"budget_{int(budget)}_score"
            if preferred in data and data[preferred].shape == eval_shape:
                budget_map[int(budget)] = data[preferred].astype(np.float64)
        if budget_map:
            out[stem] = budget_map
        for key, value in data.items():
            if key.endswith("_score") and value.shape == eval_shape and not key.startswith("budget_"):
                out[f"{stem}:{key}"] = {int(budget): value.astype(np.float64) for budget in BUDGETS.astype(np.int64)}
    return out


def expand_with_calibration(
    base: dict[str, dict[int, np.ndarray]],
    single: dict[str, np.ndarray],
    depths: np.ndarray,
) -> dict[str, dict[int, np.ndarray]]:
    out: dict[str, dict[int, np.ndarray]] = {}
    keep_budget = {
        "state_generation_budget_replacement_value",
        "state_generation_budget_conditioned_value",
        "state_generation_budget_head_value",
        "state_generation_minimax_budget_policy",
        "state_generation_episode_coupled_budget_policy",
    }
    for name, scores in base.items():
        if name in keep_budget:
            out[name] = scores
    keep_single = {
        "assignment_priority_residual",
        "episode_assignment_value",
        "episode_regret",
        "episode_allocation",
        "allocation_native",
        "geometry_option_conditioned",
        "benefit_selector",
    }
    for name, score in single.items():
        if name in keep_single:
            out[name] = {int(budget): score.astype(np.float64) for budget in BUDGETS.astype(np.int64)}
    names = sorted(set(single).intersection(keep_single))
    anchor_names = [name for name in names if name in {"assignment_priority_residual", "episode_assignment_value", "residual_priority", "budget_priority"}]
    target_names = [name for name in names if name in {"episode_regret", "episode_allocation", "allocation_native", "geometry_option_conditioned"}]
    weights = [0.50]
    for left in anchor_names:
        for right in target_names:
            if left == right:
                continue
            for w in weights:
                score = float(w) * single[left].astype(np.float64) + (1.0 - float(w)) * single[right].astype(np.float64)
                out[f"mix:{left}:{right}:{w:.2f}"] = {int(budget): score for budget in BUDGETS.astype(np.int64)}
    return out


def summarize_scores(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    hard_mask: np.ndarray,
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    hard = candidate_gap.summarize_candidate(
        split,
        scores[3],
        split["option_error"].astype(np.float64),
        hard_mask,
        seed=seed,
        samples=samples,
    )
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    for budget_index, multiplier in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = candidate_gap.episode_values(split, split["option_error"].astype(np.float64), hard_mask, int(multiplier))
        score_eps, score_values = candidate_gap.episode_values(split, scores[int(multiplier)], hard_mask, int(multiplier))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {multiplier}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{int(multiplier)}"] = {
            "score_delta": candidate_gap.bootstrap_mean(score_values, seed=seed + 1009 * budget_index, samples=samples),
            "oracle_delta": candidate_gap.bootstrap_mean(oracle_values, seed=seed + 1009 * budget_index + 17, samples=samples),
            "regret_to_oracle": candidate_gap.bootstrap_mean(regret, seed=seed + 1009 * budget_index + 31, samples=samples),
            "headroom_capture_ratio": clean_float(float(capture)),
        }
    return {
        "budgets": budgets,
        "summary": {
            "mean_capture_ratio": clean_float(float(np.mean(captures))),
            "min_capture_ratio": clean_float(float(np.min(captures))),
            "max_capture_ratio": clean_float(float(np.max(captures))),
            "mean_regret_to_oracle": clean_float(float(np.mean(regrets))),
            "budget2_capture_ratio": clean_float(float(captures[0])),
            "budget3_capture_ratio": clean_float(float(captures[1])),
            "budget4_capture_ratio": clean_float(float(captures[2])),
            "legacy_budget3_summary": hard["summary"]["budget3_capture_ratio"],
        },
    }


def observed_summary(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    mask: np.ndarray,
) -> dict[str, float]:
    captures: list[float] = []
    regrets: list[float] = []
    for multiplier in BUDGETS.astype(np.int64):
        _, oracle_values = candidate_gap.episode_values(split, split["option_error"].astype(np.float64), mask, int(multiplier))
        _, score_values = candidate_gap.episode_values(split, scores[int(multiplier)], mask, int(multiplier))
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        captures.append(score_mean / oracle_mean if oracle_mean < 0.0 else 0.0)
        regrets.append(float(np.mean(score_values - oracle_values)))
    return {
        "mean_capture_ratio": clean_float(float(np.mean(captures))),
        "min_capture_ratio": clean_float(float(np.min(captures))),
        "max_capture_ratio": clean_float(float(np.max(captures))),
        "mean_regret_to_oracle": clean_float(float(np.mean(regrets))),
        "budget2_capture_ratio": clean_float(float(captures[0])),
        "budget3_capture_ratio": clean_float(float(captures[1])),
        "budget4_capture_ratio": clean_float(float(captures[2])),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    best = report["diagnosis"]
    lines = [
        "# State-Generation Global Assignment Transfer",
        "",
        f"- candidate count: `{report['candidate_count']}`",
        f"- selected by non-hard slice: `{best['selected_candidate']}`",
        "",
        "| slice | mean capture | budget-2 capture | budget-3 capture | budget-4 capture | mean regret |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for slice_name in ["selection_non_hard", "heldout_hard"]:
        row = report[slice_name]["summary"]
        lines.append(
            f"| `{slice_name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {row['mean_regret_to_oracle']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Select global assignment score families on non-hard episodes and evaluate hard transfer")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=1811)
    parser.add_argument("--bootstrap-samples", type=int, default=500)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    non_hard_mask = ~hard_mask
    eval_shape = eval_split["option_error"].shape
    single = candidate_single_scores(eval_shape)
    budget_candidates = budget_score_candidates(eval_shape)
    candidates = expand_with_calibration(budget_candidates, single, depths)
    rows: dict[str, Any] = {}
    ranking = []
    compatible: dict[str, dict[int, np.ndarray]] = {}
    for name, scores in sorted(candidates.items()):
        if all(int(budget) in scores for budget in BUDGETS.astype(np.int64)):
            compatible[name] = scores
            ranking.append({"candidate": name, **observed_summary(eval_split, scores, non_hard_mask)})
    ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    if not ranking:
        raise RuntimeError("no compatible candidate scores found")
    selected = str(ranking[0]["candidate"])
    selected_scores = compatible[selected]
    rows[selected] = {
        "selection_non_hard": summarize_scores(
            eval_split,
            selected_scores,
            non_hard_mask,
            seed=int(args.seed),
            samples=int(args.bootstrap_samples),
        ),
        "heldout_hard": summarize_scores(
            eval_split,
            selected_scores,
            hard_mask,
            seed=int(args.seed) + 5000,
            samples=int(args.bootstrap_samples),
        ),
    }
    selected_hard = rows[selected]["heldout_hard"]["summary"]
    selected_non_hard = rows[selected]["selection_non_hard"]["summary"]
    hard_closes = bool(float(selected_hard["mean_capture_ratio"]) >= 0.5 and float(selected_hard["min_capture_ratio"]) > 0.0)
    transfers_positive = bool(float(selected_hard["mean_capture_ratio"]) > 0.0 and float(selected_hard["budget4_capture_ratio"]) > 0.0)
    if hard_closes:
        verdict = (
            "Non-hard selected global assignment calibration captures substantial hard oracle headroom. "
            "Independent export validation remains required."
        )
    elif transfers_positive:
        verdict = (
            "Non-hard selected global assignment calibration transfers a positive hard signal, but allocation closure remains open."
        )
    else:
        verdict = (
            "Non-hard selected global assignment calibration does not transfer to the hard exact-budget boundary; allocation remains open."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_global_assignment_transfer",
        "config": {
            "seed": int(args.seed),
            "bootstrap_samples": int(args.bootstrap_samples),
            "budget_multipliers": BUDGETS.tolist(),
            "selection": "rank candidates by non-hard mean oracle-headroom capture; evaluate selected candidate on held-out hard episodes",
        },
        "candidate_count": int(len(compatible)),
        "hard_episode_union": hard_episodes,
        "ranking_top": ranking[:25],
        "selection_non_hard": rows[selected]["selection_non_hard"],
        "heldout_hard": rows[selected]["heldout_hard"],
        "diagnosis": {
            "global_assignment_transfer_closes": hard_closes,
            "global_assignment_transfer_positive": transfers_positive,
            "selected_candidate": selected,
            "selected_non_hard_mean_capture_ratio": clean_float(float(selected_non_hard["mean_capture_ratio"])),
            "selected_hard_mean_capture_ratio": clean_float(float(selected_hard["mean_capture_ratio"])),
            "selected_hard_budget2_capture_ratio": clean_float(float(selected_hard["budget2_capture_ratio"])),
            "selected_hard_budget3_capture_ratio": clean_float(float(selected_hard["budget3_capture_ratio"])),
            "selected_hard_budget4_capture_ratio": clean_float(float(selected_hard["budget4_capture_ratio"])),
            "selected_hard_mean_regret_to_oracle": clean_float(float(selected_hard["mean_regret_to_oracle"])),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "candidate_scores": "fixed eval score artifacts only; no network retraining",
            "selection": "non-hard eval episodes select the candidate family; hard episodes are held out from selection",
            "oracle_scope": "eval option_error is used for non-hard selection and hard evaluation after fixed score generation",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": [
            "deployable allocation policy",
            "independent export validation",
            "complete BEDC-native world model",
            "training-free proof of allocation closure",
        ],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        hard_mask=hard_mask.astype(bool),
        selected_candidate=np.asarray([selected]),
        **{f"budget_{int(k)}_score": selected_scores[int(k)].astype(np.float64) for k in BUDGETS.astype(np.int64)},
    )
    Path(args.json).write_text(
        json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
