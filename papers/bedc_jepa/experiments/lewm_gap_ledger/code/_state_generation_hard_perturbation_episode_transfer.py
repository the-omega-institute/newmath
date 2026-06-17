from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_candidate_oracle_gap as candidate_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_global_assignment_transfer as global_transfer
import _state_generation_hard_perturbation_value_learner as learner


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_perturbation_episode_transfer.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_perturbation_episode_transfer.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_hard_perturbation_episode_transfer_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
LEARNER_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
FIXED_PRED = REPORT_DIR / "state_generation_global_assignment_transfer_predictions.npz"
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


def depth_bias(score: np.ndarray, depths: np.ndarray, lam: float, power: int) -> np.ndarray:
    centered = (depths.astype(np.float64) - 3.0) / 2.0
    token = centered if int(power) == 1 else centered * centered
    return (score.astype(np.float64) + float(lam) * token[None, :]).astype(np.float64)


def per_depth_scale(score: np.ndarray, weights: np.ndarray) -> np.ndarray:
    return (score.astype(np.float64) * weights.astype(np.float64)[None, :]).astype(np.float64)


def anchor_rank(score: np.ndarray) -> np.ndarray:
    out = np.zeros_like(score, dtype=np.float64)
    for row in range(score.shape[0]):
        order = np.argsort(score[row], kind="mergesort")
        ranks = np.zeros(score.shape[1], dtype=np.float64)
        ranks[order] = np.arange(score.shape[1], dtype=np.float64)
        out[row] = ranks / float(max(score.shape[1] - 1, 1))
    return out


def episode_depth_centered(split: dict[str, np.ndarray], score: np.ndarray) -> np.ndarray:
    out = score.astype(np.float64).copy()
    episode = split["episode"].astype(np.int64)
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        block = out[idx]
        depth_mean = np.mean(block, axis=0, keepdims=True)
        depth_scale = np.std(block, axis=0, keepdims=True)
        depth_scale[depth_scale < 1.0e-6] = 1.0
        out[idx] = (block - depth_mean) / depth_scale
    return out.astype(np.float64)


def candidate_scores(
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    learner_scores: dict[int, np.ndarray],
    fixed_scores: dict[int, np.ndarray],
) -> dict[str, dict[int, np.ndarray]]:
    out: dict[str, dict[int, np.ndarray]] = {"learner_base": learner_scores}
    for lam in (-0.25, -0.15, -0.08, -0.04, 0.04, 0.08, 0.15, 0.25):
        out[f"learner_depth_linear_{lam:+.2f}"] = {
            int(budget): depth_bias(learner_scores[int(budget)], depths, lam, 1) for budget in BUDGETS
        }
        out[f"learner_depth_quadratic_{lam:+.2f}"] = {
            int(budget): depth_bias(learner_scores[int(budget)], depths, lam, 2) for budget in BUDGETS
        }
    scale_rows = {
        "shallow_down": np.asarray([0.75, 0.90, 1.00, 1.05, 1.10], dtype=np.float64),
        "deep_down": np.asarray([1.10, 1.05, 1.00, 0.90, 0.75], dtype=np.float64),
        "middle_up": np.asarray([1.05, 0.95, 0.80, 0.95, 1.05], dtype=np.float64),
        "middle_down": np.asarray([0.90, 1.00, 1.15, 1.00, 0.90], dtype=np.float64),
    }
    for name, weights in scale_rows.items():
        out[f"learner_depth_scale_{name}"] = {
            int(budget): per_depth_scale(learner_scores[int(budget)], weights) for budget in BUDGETS
        }
    rank_scores = {int(budget): anchor_rank(learner_scores[int(budget)]) for budget in BUDGETS}
    out["learner_anchor_rank"] = rank_scores
    for lam in (-0.20, -0.10, 0.10, 0.20):
        out[f"learner_anchor_rank_depth_{lam:+.2f}"] = {
            int(budget): depth_bias(rank_scores[int(budget)], depths, lam, 1) for budget in BUDGETS
        }
    centered = {int(budget): episode_depth_centered(split, learner_scores[int(budget)]) for budget in BUDGETS}
    out["learner_episode_depth_centered"] = centered
    for lam in (-0.20, -0.10, 0.10, 0.20):
        out[f"learner_episode_depth_centered_bias_{lam:+.2f}"] = {
            int(budget): depth_bias(centered[int(budget)], depths, lam, 1) for budget in BUDGETS
        }
    for w in (0.25, 0.50, 0.75):
        out[f"mix_learner_fixed_{w:.2f}"] = {
            int(budget): float(w) * learner_scores[int(budget)] + (1.0 - float(w)) * fixed_scores[int(budget)]
            for budget in BUDGETS
        }
    return out


def summarize_candidate(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    mask: np.ndarray,
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    summary = global_transfer.observed_summary(split, scores, mask.astype(bool))
    budgets: dict[str, Any] = {}
    for budget_index, budget in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = candidate_gap.episode_values(split, split["option_error"].astype(np.float64), mask, int(budget))
        score_eps, score_values = candidate_gap.episode_values(split, scores[int(budget)], mask, int(budget))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {budget}")
        budgets[f"budget_{int(budget)}"] = {
            "score_delta": candidate_gap.bootstrap_mean(score_values, seed=seed + 1009 * budget_index, samples=samples),
            "oracle_delta": candidate_gap.bootstrap_mean(oracle_values, seed=seed + 1009 * budget_index + 17, samples=samples),
            "regret_to_oracle": candidate_gap.bootstrap_mean(score_values - oracle_values, seed=seed + 1009 * budget_index + 31, samples=samples),
            "headroom_capture_ratio": summary[f"budget{int(budget)}_capture_ratio"],
        }
    return {"summary": summary, "budgets": budgets}


def hard_alignment(split: dict[str, np.ndarray], depths: np.ndarray, hard_episodes: list[int], scores: dict[int, np.ndarray]) -> dict[str, Any]:
    return learner.hard_label_alignment(split, depths, BUDGETS, hard_episodes, scores)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    selected = report["diagnosis"]["selected_candidate"]
    hard = report["heldout_hard"]["summary"]
    lines = [
        "# State-Generation Hard Perturbation Episode Transfer",
        "",
        f"- selected candidate: `{selected}`",
        f"- candidate count: `{report['candidate_count']}`",
        "",
        "| slice | mean capture | budget-2 | budget-3 | budget-4 | mean regret | label rho |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    non = report["selection_non_hard"]["summary"]
    lines.append(
        f"| `selection_non_hard` | {non['mean_capture_ratio']:.6g} | {non['budget2_capture_ratio']:.6g} | "
        f"{non['budget3_capture_ratio']:.6g} | {non['budget4_capture_ratio']:.6g} | {non['mean_regret_to_oracle']:.6g} | NA |"
    )
    lines.append(
        f"| `heldout_hard` | {hard['mean_capture_ratio']:.6g} | {hard['budget2_capture_ratio']:.6g} | "
        f"{hard['budget3_capture_ratio']:.6g} | {hard['budget4_capture_ratio']:.6g} | {hard['mean_regret_to_oracle']:.6g} | "
        f"{report['hard_label_alignment']['mean_score_label_spearman']:.6g} |"
    )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Select episode/depth transforms for perturbation-value scores on non-hard episodes and test hard transfer")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--learner-pred", default=str(LEARNER_PRED))
    parser.add_argument("--fixed-pred", default=str(FIXED_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2099)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    non_hard_mask = ~hard_mask
    learner_pred = load_npz(Path(args.learner_pred))
    fixed_pred = load_npz(Path(args.fixed_pred))
    learner_scores = {int(budget): learner_pred[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    fixed_scores = {int(budget): fixed_pred[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    candidates = candidate_scores(split, depths, learner_scores, fixed_scores)
    ranking: list[dict[str, Any]] = []
    for index, (name, scores) in enumerate(sorted(candidates.items())):
        del index
        non_hard_summary = global_transfer.observed_summary(split, scores, non_hard_mask)
        ranking.append({"candidate": name, **non_hard_summary})
    ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    selected = str(ranking[0]["candidate"])
    selected_scores = candidates[selected]
    selected_non_hard = summarize_candidate(split, selected_scores, non_hard_mask, seed=int(args.seed) + 1000, samples=int(args.bootstrap_samples))
    selected_hard = summarize_candidate(split, selected_scores, hard_mask, seed=int(args.seed) + 2000, samples=int(args.bootstrap_samples))
    selected_alignment = hard_alignment(split, depths, hard_episodes, selected_scores)
    base_hard = summarize_candidate(split, learner_scores, hard_mask, seed=int(args.seed) + 9000, samples=int(args.bootstrap_samples))
    closes = bool(
        float(selected_hard["summary"]["mean_capture_ratio"]) > 0.0
        and float(selected_hard["summary"]["min_capture_ratio"]) > 0.0
        and float(selected_alignment["mean_score_label_spearman"]) > 0.35
    )
    transfer_improves = bool(
        float(selected_hard["summary"]["mean_capture_ratio"]) > float(base_hard["summary"]["mean_capture_ratio"])
    )
    verdict = (
        "Episode/depth transfer calibration closes the hard perturbation-value assignment gate on this export; independent export validation is required."
        if closes
        else "Episode/depth transfer calibration improves the perturbation-value learner on the hard slice but does not close all-budget hard allocation."
        if transfer_improves
        else "Episode/depth transfer calibration selected on non-hard episodes does not improve hard perturbation-value allocation transfer."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_perturbation_episode_transfer",
        "candidate_count": int(len(candidates)),
        "selection_non_hard": selected_non_hard,
        "heldout_hard": selected_hard,
        "base_learner_hard": base_hard,
        "hard_label_alignment": selected_alignment,
        "ranking": ranking[:12],
        "diagnosis": {
            "selected_candidate": selected,
            "hard_perturbation_episode_transfer_closes": closes,
            "hard_transfer_improves_base_learner": transfer_improves,
            "selected_hard_mean_capture_ratio": selected_hard["summary"]["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_hard["summary"]["mean_capture_ratio"],
            "selected_hard_mean_regret_to_oracle": selected_hard["summary"]["mean_regret_to_oracle"],
            "selected_hard_label_spearman": selected_alignment["mean_score_label_spearman"],
        },
        "verdict": verdict,
        "leakage_attestation": {
            "selection": "candidate selection uses non-hard eval episodes; held-out hard episodes are used only for transfer evaluation",
            "oracle_scope": "eval option_error is used for non-hard calibration selection and hard diagnostic evaluation, not for deployable training",
            "training": "no model training is performed; this is an episode/depth transfer audit over fixed scores",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure beyond this export", "deployable policy", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(
        Path(args.out),
        **{f"budget_{int(budget)}_score": selected_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
