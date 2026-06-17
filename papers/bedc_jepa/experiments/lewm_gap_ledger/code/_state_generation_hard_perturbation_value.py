from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_perturbation_value.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_perturbation_value.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
TRANSFER_PRED = REPORT_DIR / "state_generation_global_assignment_transfer_predictions.npz"
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


def exact_cost(option_score: np.ndarray, depths: np.ndarray, target: int) -> float:
    n = option_score.shape[0]
    dp = np.full((n + 1, target + 1), np.inf, dtype=np.float64)
    dp[0, 0] = 0.0
    for row in range(n):
        for budget in range(target + 1):
            base = float(dp[row, budget])
            if not math.isfinite(base):
                continue
            for col, depth in enumerate(depths.astype(np.int64)):
                new_budget = budget + int(depth)
                if new_budget > target:
                    continue
                value = base + float(option_score[row, col])
                if value < dp[row + 1, new_budget]:
                    dp[row + 1, new_budget] = value
    out = float(dp[n, target])
    if not math.isfinite(out):
        raise RuntimeError("infeasible exact-budget target")
    return out


def forced_delta_labels(option_error: np.ndarray, depths: np.ndarray, target: int) -> np.ndarray:
    base_cost = exact_cost(option_error, depths, target)
    labels = np.zeros_like(option_error, dtype=np.float64)
    infeasible = float(np.max(option_error) - np.min(option_error) + 1.0)
    for row in range(option_error.shape[0]):
        residual = np.delete(option_error, row, axis=0)
        for col, depth in enumerate(depths.astype(np.int64)):
            residual_target = target - int(depth)
            if residual_target < 0:
                labels[row, col] = infeasible
                continue
            if len(residual) == 0:
                residual_cost = 0.0 if residual_target == 0 else np.inf
            else:
                try:
                    residual_cost = exact_cost(residual, depths, residual_target)
                except RuntimeError:
                    residual_cost = np.inf
            forced = float(option_error[row, col]) + float(residual_cost)
            labels[row, col] = clean_float(forced - base_cost) if math.isfinite(forced) else infeasible
    labels[labels < 0.0] = 0.0
    return labels.astype(np.float64)


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    def rank(v: np.ndarray) -> np.ndarray:
        order = np.argsort(v.astype(np.float64), kind="mergesort")
        ranks = np.zeros(len(v), dtype=np.float64)
        ranks[order] = np.arange(len(v), dtype=np.float64)
        return ranks

    if len(x) < 2:
        return 0.0
    rx = rank(x)
    ry = rank(y)
    if float(np.std(rx)) <= 1.0e-12 or float(np.std(ry)) <= 1.0e-12:
        return 0.0
    return clean_float(float(np.corrcoef(rx, ry)[0, 1]))


def depth_means(labels: np.ndarray, depths: np.ndarray) -> dict[str, float]:
    out: dict[str, float] = {}
    for col, depth in enumerate(depths.astype(np.int64)):
        out[str(int(depth))] = clean_float(float(np.mean(labels[:, col])))
    return out


def budget_row(
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    hard_episodes: list[int],
    selected_score: np.ndarray,
    budget: int,
) -> dict[str, Any]:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    hard_set = set(int(ep) for ep in hard_episodes)
    all_labels: list[np.ndarray] = []
    all_scores: list[np.ndarray] = []
    selected_label_values: list[float] = []
    oracle_label_values: list[float] = []
    episode_rows: list[dict[str, Any]] = []

    chosen = budget_audit.exact_budget_choice_at_multiplier(episode, selected_score, depths, int(budget))
    oracle = budget_audit.exact_budget_choice_at_multiplier(episode, option_error, depths, int(budget))

    for ep in sorted(hard_set):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        if len(idx) == 0:
            continue
        target = int(budget * len(idx))
        local_error = option_error[idx]
        local_score = selected_score[idx]
        labels = forced_delta_labels(local_error, depths, target)
        local_chosen = chosen[idx].astype(np.int64)
        local_oracle = oracle[idx].astype(np.int64)
        selected_values = labels[np.arange(len(idx)), local_chosen]
        oracle_values = labels[np.arange(len(idx)), local_oracle]
        all_labels.append(labels.reshape(-1))
        all_scores.append(local_score.reshape(-1))
        selected_label_values.extend(float(v) for v in selected_values)
        oracle_label_values.extend(float(v) for v in oracle_values)
        episode_rows.append(
            {
                "episode": int(ep),
                "anchors": int(len(idx)),
                "label_iqr": clean_float(float(np.quantile(labels, 0.75) - np.quantile(labels, 0.25))),
                "label_p90": clean_float(float(np.quantile(labels, 0.90))),
                "score_label_spearman": spearman(local_score.reshape(-1), labels.reshape(-1)),
                "selected_forced_delta_mean": clean_float(float(np.mean(selected_values))),
                "oracle_forced_delta_mean": clean_float(float(np.mean(oracle_values))),
                "selected_depth_counts": {
                    str(int(k)): int(v) for k, v in zip(*np.unique(depths[local_chosen], return_counts=True))
                },
                "oracle_depth_counts": {
                    str(int(k)): int(v) for k, v in zip(*np.unique(depths[local_oracle], return_counts=True))
                },
            }
        )

    labels_flat = np.concatenate(all_labels).astype(np.float64)
    scores_flat = np.concatenate(all_scores).astype(np.float64)
    positive_mass = float(np.sum(labels_flat[labels_flat > 1.0e-12]))
    top_count = max(1, int(math.ceil(0.10 * len(labels_flat))))
    top_mass = float(np.sum(np.sort(labels_flat)[-top_count:]))
    return {
        "budget": int(budget),
        "hard_anchor_count": int(sum(int(row["anchors"]) for row in episode_rows)),
        "label_mean": clean_float(float(np.mean(labels_flat))),
        "label_iqr": clean_float(float(np.quantile(labels_flat, 0.75) - np.quantile(labels_flat, 0.25))),
        "label_p90": clean_float(float(np.quantile(labels_flat, 0.90))),
        "near_zero_fraction": clean_float(float(np.mean(labels_flat <= 1.0e-12))),
        "top_decile_mass_fraction": clean_float(float(top_mass / positive_mass)) if positive_mass > 0.0 else 0.0,
        "score_label_spearman": spearman(scores_flat, labels_flat),
        "selected_forced_delta_mean": clean_float(float(np.mean(np.asarray(selected_label_values, dtype=np.float64)))),
        "oracle_forced_delta_mean": clean_float(float(np.mean(np.asarray(oracle_label_values, dtype=np.float64)))),
        "forced_delta_depth_means": depth_means(np.concatenate([x.reshape(-1, len(depths)) for x in all_labels]), depths),
        "episodes": episode_rows,
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Hard Perturbation-Value Audit",
        "",
        "| budget | label iqr | label p90 | zero frac | top-decile mass | score-label rho | selected delta |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for row in report["budget_rows"]:
        lines.append(
            f"| `{row['budget']}` | {row['label_iqr']:.6g} | {row['label_p90']:.6g} | "
            f"{row['near_zero_fraction']:.6g} | {row['top_decile_mass_fraction']:.6g} | "
            f"{row['score_label_spearman']:.6g} | {row['selected_forced_delta_mean']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Construct hard-regime exact-budget perturbation value labels")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--transfer-pred", default=str(TRANSFER_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    pred = load_npz(Path(args.transfer_pred))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    rows = [
        budget_row(split, depths, hard_episodes, pred[f"budget_{int(budget)}_score"].astype(np.float64), int(budget))
        for budget in BUDGETS
    ]
    min_iqr = min(float(row["label_iqr"]) for row in rows)
    max_zero = max(float(row["near_zero_fraction"]) for row in rows)
    mean_rho = float(np.mean([float(row["score_label_spearman"]) for row in rows]))
    labels_available = bool(min_iqr > 1.0e-5 and max_zero < 0.95)
    fixed_score_strong = bool(mean_rho >= 0.50 and all(float(row["score_label_spearman"]) >= 0.35 for row in rows))
    verdict = (
        "Hard-regime forced-option perturbation labels are non-degenerate and the fixed selected score is already strongly aligned with them. "
        "This supports training directly on perturbation value labels, but does not close allocation without a learned policy."
        if labels_available and fixed_score_strong
        else "Hard-regime forced-option perturbation labels are non-degenerate, while the fixed selected score is not strongly aligned with them. "
        "This identifies a direct compute-value supervision target for the hard exact-budget boundary."
        if labels_available
        else "Hard-regime forced-option perturbation labels are too sparse or degenerate under this export; the hard allocation boundary needs a different value construction."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_perturbation_value",
        "hard_episode_union": hard_episodes,
        "budget_rows": rows,
        "summary": {
            "hard_perturbation_labels_available": labels_available,
            "fixed_score_strongly_aligned": fixed_score_strong,
            "min_label_iqr": clean_float(min_iqr),
            "max_near_zero_fraction": clean_float(max_zero),
            "mean_score_label_spearman": clean_float(mean_rho),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "oracle_scope": "eval option_error is used to construct diagnostic forced-option value labels only",
            "selection": "uses the already fixed fi-084 selected score; no policy is selected by the perturbation labels",
            "budget_stress": "budgets 2, 3, and 4 are fixed before measuring labels",
            "training": "no model training is performed",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure", "deployable policy", "independent export validation", "complete BEDC-native world model"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
