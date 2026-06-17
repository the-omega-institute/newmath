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
import _state_generation_hard_perturbation_value as hard_value


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_assignment_mechanism_labels.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_assignment_mechanism_labels.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
LEARNER_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
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


def entropy_from_counts(counts: np.ndarray) -> float:
    total = float(np.sum(counts))
    if total <= 0.0:
        return 0.0
    p = counts.astype(np.float64) / total
    p = p[p > 0.0]
    return clean_float(float(-np.sum(p * np.log(p)) / math.log(len(counts)))) if len(counts) else 0.0


def depth_counts(choice: np.ndarray, depths: np.ndarray) -> np.ndarray:
    return np.asarray([int(np.sum(depths[choice] == int(depth))) for depth in depths.astype(np.int64)], dtype=np.int64)


def selected_rate(option_error: np.ndarray, choice: np.ndarray, depths: np.ndarray) -> float:
    chosen_error = option_error[np.arange(len(choice)), choice.astype(np.int64)]
    chosen_steps = depths[choice.astype(np.int64)].astype(np.float64)
    return clean_float(float(np.sum(chosen_error) / np.sum(chosen_steps)))


def uniform_rate(option_error: np.ndarray, depths: np.ndarray, budget: int) -> float:
    col = int(np.where(depths.astype(np.int64) == int(budget))[0][0])
    return clean_float(float(np.sum(option_error[:, col]) / float(int(budget) * len(option_error))))


def episode_mechanism_rows(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    depths: np.ndarray,
    hard_episodes: list[int],
) -> list[dict[str, Any]]:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    hard = set(int(ep) for ep in hard_episodes)
    rows: list[dict[str, Any]] = []
    for ep in sorted(int(v) for v in np.unique(episode)):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        local_error = option_error[idx]
        for budget in BUDGETS.astype(np.int64):
            oracle = budget_audit.exact_budget_choice_at_multiplier(episode[idx], local_error, depths, int(budget))
            selected = budget_audit.exact_budget_choice_at_multiplier(episode[idx], scores[int(budget)][idx], depths, int(budget))
            labels = hard_value.forced_delta_labels(local_error, depths, int(budget) * len(idx))
            oracle_counts = depth_counts(oracle, depths)
            selected_counts = depth_counts(selected, depths)
            count_l1 = float(np.sum(np.abs(oracle_counts - selected_counts))) / float(max(len(idx), 1))
            selected_forced = labels[np.arange(len(idx)), selected.astype(np.int64)]
            oracle_forced = labels[np.arange(len(idx)), oracle.astype(np.int64)]
            positive_mass = float(np.sum(labels[labels > 1.0e-12]))
            top_count = max(1, int(math.ceil(0.10 * labels.size)))
            top_mass = float(np.sum(np.sort(labels.reshape(-1))[-top_count:]))
            rows.append(
                {
                    "episode": int(ep),
                    "budget": int(budget),
                    "hard": bool(int(ep) in hard),
                    "anchors": int(len(idx)),
                    "oracle_minus_uniform": clean_float(selected_rate(local_error, oracle, depths) - uniform_rate(local_error, depths, int(budget))),
                    "selected_minus_oracle": clean_float(selected_rate(local_error, selected, depths) - selected_rate(local_error, oracle, depths)),
                    "oracle_depth_entropy": entropy_from_counts(oracle_counts),
                    "selected_depth_entropy": entropy_from_counts(selected_counts),
                    "depth_count_l1_per_anchor": clean_float(count_l1),
                    "oracle_uses_depth1_fraction": clean_float(float(np.mean(depths[oracle] == 1))),
                    "oracle_uses_depth5_fraction": clean_float(float(np.mean(depths[oracle] == 5))),
                    "selected_uses_depth1_fraction": clean_float(float(np.mean(depths[selected] == 1))),
                    "selected_uses_depth5_fraction": clean_float(float(np.mean(depths[selected] == 5))),
                    "forced_delta_iqr": clean_float(float(np.quantile(labels, 0.75) - np.quantile(labels, 0.25))),
                    "forced_delta_top_decile_mass_fraction": clean_float(float(top_mass / positive_mass)) if positive_mass > 0.0 else 0.0,
                    "selected_forced_delta_mean": clean_float(float(np.mean(selected_forced))),
                    "oracle_forced_delta_mean": clean_float(float(np.mean(oracle_forced))),
                    "oracle_depth_counts": {str(int(depth)): int(count) for depth, count in zip(depths.astype(np.int64), oracle_counts)},
                    "selected_depth_counts": {str(int(depth)): int(count) for depth, count in zip(depths.astype(np.int64), selected_counts)},
                }
            )
    return rows


def mean_row(rows: list[dict[str, Any]], key: str) -> float:
    if not rows:
        return 0.0
    return clean_float(float(np.mean([float(row[key]) for row in rows])))


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    hard_rows = [row for row in rows if bool(row["hard"])]
    non_rows = [row for row in rows if not bool(row["hard"])]
    keys = [
        "oracle_minus_uniform",
        "selected_minus_oracle",
        "oracle_depth_entropy",
        "depth_count_l1_per_anchor",
        "oracle_uses_depth1_fraction",
        "oracle_uses_depth5_fraction",
        "forced_delta_iqr",
        "forced_delta_top_decile_mass_fraction",
        "selected_forced_delta_mean",
    ]
    out: dict[str, Any] = {}
    for key in keys:
        hard_mean = mean_row(hard_rows, key)
        non_mean = mean_row(non_rows, key)
        out[key] = {
            "hard_mean": hard_mean,
            "non_hard_mean": non_mean,
            "hard_minus_non_hard": clean_float(hard_mean - non_mean),
        }
    hard_budget = {str(int(budget)): [row for row in hard_rows if int(row["budget"]) == int(budget)] for budget in BUDGETS}
    out["hard_by_budget"] = {
        str(int(budget)): {
            "selected_minus_oracle": mean_row(subrows, "selected_minus_oracle"),
            "depth_count_l1_per_anchor": mean_row(subrows, "depth_count_l1_per_anchor"),
            "forced_delta_iqr": mean_row(subrows, "forced_delta_iqr"),
            "forced_delta_top_decile_mass_fraction": mean_row(subrows, "forced_delta_top_decile_mass_fraction"),
        }
        for budget, subrows in hard_budget.items()
    }
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    s = report["summary"]
    lines = [
        "# State-Generation Hard Assignment Mechanism Labels",
        "",
        "| mechanism label | hard mean | non-hard mean | hard - non-hard |",
        "|---|---:|---:|---:|",
    ]
    for key in [
        "oracle_depth_entropy",
        "depth_count_l1_per_anchor",
        "forced_delta_top_decile_mass_fraction",
        "selected_forced_delta_mean",
        "selected_minus_oracle",
    ]:
        row = s[key]
        lines.append(f"| `{key}` | {row['hard_mean']:.6g} | {row['non_hard_mean']:.6g} | {row['hard_minus_non_hard']:.6g} |")
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Extract hard-regime exact-budget assignment mechanism labels")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--learner-pred", default=str(LEARNER_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    pred = load_npz(Path(args.learner_pred))
    scores = {int(budget): pred[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    rows = episode_mechanism_rows(split, scores, depths, hard_episodes)
    summary = summarize(rows)
    hard_mechanism_gap = bool(
        abs(float(summary["depth_count_l1_per_anchor"]["hard_minus_non_hard"])) >= 0.05
        or abs(float(summary["forced_delta_top_decile_mass_fraction"]["hard_minus_non_hard"])) >= 0.05
        or abs(float(summary["selected_forced_delta_mean"]["hard_minus_non_hard"])) >= 0.02
    )
    verdict = (
        "Hard episodes expose distinct exact-budget assignment mechanism labels: the remaining boundary should be attacked with mechanism-aware assignment supervision rather than generic score calibration."
        if hard_mechanism_gap
        else "Hard episodes do not expose a strong mechanism-label shift under this audit; the remaining boundary is not explained by these assignment labels alone."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_assignment_mechanism_labels",
        "hard_episode_union": hard_episodes,
        "row_count": int(len(rows)),
        "summary": summary,
        "top_hard_regret_rows": sorted(
            [row for row in rows if bool(row["hard"])],
            key=lambda row: float(row["selected_minus_oracle"]),
            reverse=True,
        )[:10],
        "verdict": verdict,
        "leakage_attestation": {
            "oracle_scope": "eval option_error is used to extract diagnostic exact-budget assignment mechanism labels only",
            "selection": "no candidate policy is selected by hard labels",
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
