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
import _state_generation_hard_perturbation_value as hard_value
import _state_generation_hard_perturbation_value_learner as base_learner


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_assignment_structured_mechanism_transfer.json"
DEFAULT_MD = REPORT_DIR / "state_generation_assignment_structured_mechanism_transfer.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_assignment_structured_mechanism_transfer_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
MECHANISM_LEARNER_PRED = REPORT_DIR / "state_generation_mechanism_target_learner_predictions.npz"
BASE_LEARNER_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
TARGET_CEILING_PRED = REPORT_DIR / "state_generation_mechanism_aware_assignment_target_predictions.npz"
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


def load_scores(path: Path) -> dict[int, np.ndarray]:
    data = load_npz(path)
    return {int(budget): data[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}


def zscore_like(reference: np.ndarray, value: np.ndarray) -> np.ndarray:
    mean = float(np.mean(reference.astype(np.float64)))
    scale = float(np.std(reference.astype(np.float64)))
    if scale < 1.0e-6:
        scale = 1.0
    return ((value.astype(np.float64) - mean) / scale).astype(np.float64)


def rank_vector(v: np.ndarray) -> np.ndarray:
    order = np.argsort(v.astype(np.float64), kind="mergesort")
    ranks = np.zeros(len(v), dtype=np.float64)
    ranks[order] = np.arange(len(v), dtype=np.float64)
    return ranks


def episode_rank_scores(split: dict[str, np.ndarray], scores: dict[int, np.ndarray]) -> dict[int, np.ndarray]:
    episode = split["episode"].astype(np.int64)
    out = {int(budget): np.zeros_like(scores[int(budget)], dtype=np.float64) for budget in BUDGETS}
    for budget in BUDGETS.astype(np.int64):
        flat = out[int(budget)]
        for ep in np.unique(episode):
            idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
            local = scores[int(budget)][idx].reshape(-1)
            flat[idx] = rank_vector(local).reshape(len(idx), scores[int(budget)].shape[1])
    return out


def episode_zscore_scores(split: dict[str, np.ndarray], scores: dict[int, np.ndarray]) -> dict[int, np.ndarray]:
    episode = split["episode"].astype(np.int64)
    out = {int(budget): np.zeros_like(scores[int(budget)], dtype=np.float64) for budget in BUDGETS}
    for budget in BUDGETS.astype(np.int64):
        flat = out[int(budget)]
        for ep in np.unique(episode):
            idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
            local = scores[int(budget)][idx]
            flat[idx] = zscore_like(local.reshape(-1), local)
    return out


def depth_offset_scores(
    scores: dict[int, np.ndarray],
    labels: dict[int, np.ndarray],
    depths: np.ndarray,
    fit_mask: np.ndarray,
) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        corrected = scores[int(budget)].copy()
        for col, _depth in enumerate(depths.astype(np.int64)):
            residual = labels[int(budget)][fit_mask, col] - scores[int(budget)][fit_mask, col]
            offset = float(np.mean(residual.astype(np.float64))) if len(residual) else 0.0
            corrected[:, col] = corrected[:, col] + offset
        out[int(budget)] = corrected.astype(np.float64)
    return out


def depth_affine_scores(
    scores: dict[int, np.ndarray],
    labels: dict[int, np.ndarray],
    depths: np.ndarray,
    fit_mask: np.ndarray,
) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        corrected = scores[int(budget)].copy()
        for col, _depth in enumerate(depths.astype(np.int64)):
            x = scores[int(budget)][fit_mask, col].astype(np.float64)
            y = labels[int(budget)][fit_mask, col].astype(np.float64)
            if len(x) < 2 or float(np.std(x)) < 1.0e-8:
                a = 1.0
                b = float(np.mean(y - x)) if len(x) else 0.0
            else:
                a, b = np.polyfit(x, y, deg=1)
            corrected[:, col] = float(a) * corrected[:, col] + float(b)
        out[int(budget)] = corrected.astype(np.float64)
    return out


def budget_affine_scores(
    scores: dict[int, np.ndarray],
    labels: dict[int, np.ndarray],
    fit_mask: np.ndarray,
) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        x = scores[int(budget)][fit_mask].reshape(-1).astype(np.float64)
        y = labels[int(budget)][fit_mask].reshape(-1).astype(np.float64)
        if len(x) < 2 or float(np.std(x)) < 1.0e-8:
            a = 1.0
            b = float(np.mean(y - x)) if len(x) else 0.0
        else:
            a, b = np.polyfit(x, y, deg=1)
        out[int(budget)] = (float(a) * scores[int(budget)] + float(b)).astype(np.float64)
    return out


def mix_scores(a: dict[int, np.ndarray], b: dict[int, np.ndarray], alpha: float) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        za = zscore_like(a[int(budget)], a[int(budget)])
        zb = zscore_like(b[int(budget)], b[int(budget)])
        out[int(budget)] = ((1.0 - float(alpha)) * za + float(alpha) * zb).astype(np.float64)
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


def label_alignment(split: dict[str, np.ndarray], depths: np.ndarray, hard_episodes: list[int], scores: dict[int, np.ndarray]) -> dict[str, Any]:
    return base_learner.hard_label_alignment(split, depths, BUDGETS, hard_episodes, scores)


def build_candidates(
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    fit_mask: np.ndarray,
    mechanism: dict[int, np.ndarray],
    base: dict[int, np.ndarray],
    target: dict[int, np.ndarray],
) -> dict[str, dict[int, np.ndarray]]:
    labels = base_learner.forced_delta_targets(split, depths, BUDGETS)
    out: dict[str, dict[int, np.ndarray]] = {
        "mechanism_raw": mechanism,
        "base_perturbation_value": base,
        "mechanism_episode_rank": episode_rank_scores(split, mechanism),
        "mechanism_episode_zscore": episode_zscore_scores(split, mechanism),
        "mechanism_budget_affine_nonhard": budget_affine_scores(mechanism, labels, fit_mask),
        "mechanism_depth_offset_nonhard": depth_offset_scores(mechanism, labels, depths, fit_mask),
        "mechanism_depth_affine_nonhard": depth_affine_scores(mechanism, labels, depths, fit_mask),
    }
    for alpha in (0.25, 0.50, 0.75):
        out[f"mix_mechanism_base_{alpha:.2f}"] = mix_scores(mechanism, base, alpha)
    out["rank_then_depth_offset_nonhard"] = depth_offset_scores(out["mechanism_episode_rank"], labels, depths, fit_mask)
    out["zscore_then_depth_offset_nonhard"] = depth_offset_scores(out["mechanism_episode_zscore"], labels, depths, fit_mask)
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Assignment-Structured Mechanism Transfer",
        "",
        f"- selected non-hard transform: `{report['diagnosis']['selected_candidate']}`",
        f"- candidate count: `{report['candidate_count']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["selected", "mechanism_raw", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit assignment-structured transforms of non-leaky mechanism scores")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--mechanism-pred", default=str(MECHANISM_LEARNER_PRED))
    parser.add_argument("--base-pred", default=str(BASE_LEARNER_PRED))
    parser.add_argument("--target-pred", default=str(TARGET_CEILING_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2417)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    non_hard_mask = ~hard_mask
    mechanism = load_scores(Path(args.mechanism_pred))
    base = load_scores(Path(args.base_pred))
    target = load_scores(Path(args.target_pred))
    candidates = build_candidates(split, depths, non_hard_mask, mechanism, base, target)
    ranking: list[dict[str, Any]] = []
    for name, scores in sorted(candidates.items()):
        row = global_transfer.observed_summary(split, scores, non_hard_mask)
        ranking.append({"candidate": name, **row})
    ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    selected_name = str(ranking[0]["candidate"])
    hard_rows: dict[str, Any] = {}
    row_sources = {
        "selected": candidates[selected_name],
        "mechanism_raw": candidates["mechanism_raw"],
        "base_perturbation_value": candidates["base_perturbation_value"],
        "mechanism_target_ceiling": target,
    }
    for index, (name, scores) in enumerate(row_sources.items()):
        row = summarize_candidate(split, scores, hard_mask, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples))
        row["label_alignment"] = label_alignment(split, depths, hard_episodes, scores)
        hard_rows[name] = row
    selected_non_hard = summarize_candidate(
        split,
        candidates[selected_name],
        non_hard_mask,
        seed=int(args.seed) + 9000,
        samples=int(args.bootstrap_samples),
    )
    selected_summary = hard_rows["selected"]["summary"]
    raw_summary = hard_rows["mechanism_raw"]["summary"]
    base_summary = hard_rows["base_perturbation_value"]["summary"]
    closes = bool(float(selected_summary["mean_capture_ratio"]) > 0.0 and float(selected_summary["min_capture_ratio"]) > 0.0)
    improves_raw = bool(float(selected_summary["mean_capture_ratio"]) > float(raw_summary["mean_capture_ratio"]))
    improves_base = bool(float(selected_summary["mean_capture_ratio"]) > float(base_summary["mean_capture_ratio"]))
    verdict = (
        "Assignment-structured non-hard transform selection closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "Assignment-structured transforms improve the non-leaky mechanism route but do not close the held-out hard exact-budget gate."
        if improves_raw or improves_base
        else "Assignment-structured non-hard transform selection does not improve held-out hard exact-budget transfer over the raw mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_assignment_structured_mechanism_transfer",
        "candidate_count": int(len(candidates)),
        "ranking": ranking,
        "selection_non_hard": selected_non_hard,
        "hard_rows": hard_rows,
        "diagnosis": {
            "selected_candidate": selected_name,
            "assignment_structured_transfer_closes": closes,
            "selected_hard_mean_capture_ratio": selected_summary["mean_capture_ratio"],
            "selected_hard_min_capture_ratio": selected_summary["min_capture_ratio"],
            "raw_hard_mean_capture_ratio": raw_summary["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": hard_rows["mechanism_target_ceiling"]["summary"]["mean_capture_ratio"],
            "selected_improves_raw": improves_raw,
            "selected_improves_base": improves_base,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "non_hard_selection_scope": "non-hard eval option_error constructs transfer-selection labels and assignment metrics for diagnostic transform selection",
            "hard_eval_scope": "held-out hard episodes are used only after candidate selection",
            "feature_scope": "candidate scores are transforms of previously generated non-leaky mechanism and perturbation-value predictions; the target ceiling row is reported only as a reference and is excluded from selection",
            "deployment": "not deployable policy evidence; this is an assignment-structure transfer audit",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(
        Path(args.out),
        **{f"budget_{int(budget)}_score": candidates[selected_name][int(budget)].astype(np.float32) for budget in BUDGETS},
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
