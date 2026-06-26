from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_candidate_oracle_gap as candidate_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit
import _state_generation_hard_perturbation_value_learner as base_learner


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_exact_budget_surrogate.json"
DEFAULT_MD = REPORT_DIR / "state_generation_exact_budget_surrogate.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_exact_budget_surrogate_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
SCALAR_PRED = REPORT_DIR / "state_generation_mechanism_target_learner_predictions.npz"
SET_CONTEXT_PRED = REPORT_DIR / "state_generation_set_context_mechanism_learner_predictions.npz"
BASE_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
TARGET_PRED = REPORT_DIR / "state_generation_mechanism_aware_assignment_target_predictions.npz"
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


def apply_depth_offsets(scores: dict[int, np.ndarray], offsets: dict[int, np.ndarray]) -> dict[int, np.ndarray]:
    return {int(budget): (scores[int(budget)] + offsets[int(budget)].reshape(1, -1)).astype(np.float64) for budget in BUDGETS}


def rate_for_choice(option_error: np.ndarray, depths: np.ndarray, choice: np.ndarray) -> float:
    chosen_error = option_error[np.arange(len(choice)), choice.astype(np.int64)]
    chosen_depth = depths[choice.astype(np.int64)].astype(np.float64)
    return clean_float(float(np.sum(chosen_error) / np.sum(chosen_depth)))


def episode_assignment_values(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    mask: np.ndarray,
    depths: np.ndarray,
    budget: int,
) -> tuple[list[int], np.ndarray]:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    depths = depths.astype(np.int64)
    eps: list[int] = []
    values: list[float] = []
    for ep in sorted(int(v) for v in np.unique(episode[mask.astype(bool)])):
        idx = np.flatnonzero((episode == int(ep)) & mask.astype(bool)).astype(np.int64)
        local_error = option_error[idx]
        oracle = budget_audit.exact_budget_choice_at_multiplier(episode[idx], local_error, depths, int(budget))
        chosen = budget_audit.exact_budget_choice_at_multiplier(episode[idx], scores[int(budget)][idx], depths, int(budget))
        values.append(rate_for_choice(local_error, depths, chosen) - rate_for_choice(local_error, depths, oracle))
        eps.append(int(ep))
    return eps, np.asarray(values, dtype=np.float64)


def observed_regret(split: dict[str, np.ndarray], scores: dict[int, np.ndarray], mask: np.ndarray, depths: np.ndarray) -> tuple[float, float]:
    values: list[float] = []
    max_value = 0.0
    for budget in BUDGETS.astype(np.int64):
        _eps, budget_values = episode_assignment_values(split, scores, mask, depths, int(budget))
        if len(budget_values):
            values.extend(float(v) for v in budget_values)
            max_value = max(max_value, float(np.max(budget_values)))
    return clean_float(float(np.mean(values))) if values else 0.0, clean_float(max_value)


def capture_summary(split: dict[str, np.ndarray], scores: dict[int, np.ndarray], mask: np.ndarray, *, seed: int, samples: int) -> dict[str, Any]:
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget_index, budget in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = candidate_gap.episode_values(split, oracle_score, mask.astype(bool), int(budget))
        score_eps, score_values = candidate_gap.episode_values(split, scores[int(budget)], mask.astype(bool), int(budget))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {budget}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{int(budget)}"] = {
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
            "mean_regret_to_oracle": clean_float(float(np.mean(regrets))),
            "budget2_capture_ratio": clean_float(float(captures[0])),
            "budget3_capture_ratio": clean_float(float(captures[1])),
            "budget4_capture_ratio": clean_float(float(captures[2])),
        },
    }


def candidate_offsets(depths: np.ndarray) -> list[np.ndarray]:
    d = depths.astype(np.float64)
    centered = d - float(np.mean(d))
    if float(np.std(centered)) > 1.0e-8:
        centered = centered / float(np.max(np.abs(centered)))
    shallow = centered.copy()
    deep = -centered.copy()
    middle = np.abs(centered)
    middle = middle - float(np.mean(middle))
    extremes = -middle
    return [
        np.zeros(len(depths), dtype=np.float64),
        0.35 * shallow.astype(np.float64),
        0.35 * deep.astype(np.float64),
        0.35 * middle.astype(np.float64),
        0.35 * extremes.astype(np.float64),
    ]


def fit_offsets(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    mask: np.ndarray,
    depths: np.ndarray,
) -> tuple[dict[int, np.ndarray], dict[str, Any]]:
    choices = candidate_offsets(depths)
    out: dict[int, np.ndarray] = {}
    rows: dict[str, Any] = {}
    for budget in BUDGETS.astype(np.int64):
        best_key = (float("inf"), float("inf"))
        best_offset = np.zeros(len(depths), dtype=np.float64)
        for offset in choices:
            trial = {int(b): scores[int(b)].copy() for b in BUDGETS.astype(np.int64)}
            trial[int(budget)] = trial[int(budget)] + offset.reshape(1, -1)
            _eps, values = episode_assignment_values(split, trial, mask, depths, int(budget))
            key = (float(np.mean(values)), float(np.max(values)) if len(values) else 0.0)
            if key < best_key:
                best_key = key
                best_offset = offset.copy()
        out[int(budget)] = best_offset.astype(np.float64)
        rows[f"budget_{int(budget)}"] = {
            "offset_by_depth": {str(int(depth)): clean_float(float(value)) for depth, value in zip(depths.astype(np.int64), best_offset)},
            "cal_mean_assignment_regret": clean_float(best_key[0]),
            "cal_max_assignment_regret": clean_float(best_key[1]),
        }
    return out, rows


def fit_exact_budget_surrogate(
    split: dict[str, np.ndarray],
    source_rows: dict[str, dict[int, np.ndarray]],
    cal_mask: np.ndarray,
    depths: np.ndarray,
) -> tuple[str, dict[int, np.ndarray], dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    best_name = ""
    best_scores: dict[int, np.ndarray] | None = None
    best_key = (float("inf"), float("inf"))
    for name, scores in source_rows.items():
        offsets, offset_report = fit_offsets(split, scores, cal_mask, depths)
        adjusted = apply_depth_offsets(scores, offsets)
        mean_regret, max_regret = observed_regret(split, adjusted, cal_mask, depths)
        key = (mean_regret, max_regret)
        candidates.append(
            {
                "source": name,
                "cal_mean_assignment_regret": mean_regret,
                "cal_max_assignment_regret": max_regret,
                "offsets": offset_report,
            }
        )
        if key < best_key:
            best_key = key
            best_name = name
            best_scores = adjusted
    if best_scores is None:
        raise RuntimeError("no exact-budget surrogate candidate selected")
    return best_name, best_scores, {"candidates": candidates, "selection_key": [clean_float(v) for v in best_key]}


def label_alignment(split: dict[str, np.ndarray], depths: np.ndarray, hard_episodes: list[int], scores: dict[int, np.ndarray]) -> dict[str, Any]:
    return base_learner.hard_label_alignment(split, depths, BUDGETS, hard_episodes, scores)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Exact-Budget Surrogate",
        "",
        f"- selected source: `{report['diagnosis']['selected_source']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["exact_budget_surrogate", "scalar_mechanism", "set_context_mechanism", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Calibrate mechanism scores through exact-budget assignment regret")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--scalar-pred", default=str(SCALAR_PRED))
    parser.add_argument("--set-context-pred", default=str(SET_CONTEXT_PRED))
    parser.add_argument("--base-pred", default=str(BASE_PRED))
    parser.add_argument("--target-pred", default=str(TARGET_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2663)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    cal_mask = ~hard_mask
    scalar = load_scores(Path(args.scalar_pred))
    set_context = load_scores(Path(args.set_context_pred))
    base = load_scores(Path(args.base_pred))
    target = load_scores(Path(args.target_pred))
    selected_source, surrogate, selection = fit_exact_budget_surrogate(
        split,
        {
            "scalar_mechanism": scalar,
            "set_context_mechanism": set_context,
        },
        cal_mask,
        depths,
    )
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "exact_budget_surrogate": surrogate,
            "scalar_mechanism": scalar,
            "set_context_mechanism": set_context,
            "base_perturbation_value": base,
            "mechanism_target_ceiling": target,
        }.items()
    ):
        hard_rows[name] = {
            "capture": capture_summary(split, scores, hard_mask, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples)),
            "label_alignment": label_alignment(split, depths, hard_episodes, scores),
        }
    sur = hard_rows["exact_budget_surrogate"]["capture"]["summary"]
    scalar_summary = hard_rows["scalar_mechanism"]["capture"]["summary"]
    base_summary = hard_rows["base_perturbation_value"]["capture"]["summary"]
    closes = bool(float(sur["mean_capture_ratio"]) > 0.0 and float(sur["min_capture_ratio"]) > 0.0)
    improves_scalar = bool(float(sur["mean_capture_ratio"]) > float(scalar_summary["mean_capture_ratio"]))
    improves_base = bool(float(sur["mean_capture_ratio"]) > float(base_summary["mean_capture_ratio"]))
    verdict = (
        "Exact-budget surrogate calibration closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "Exact-budget surrogate calibration improves the hard mechanism route but does not close all hard exact-budget budgets."
        if improves_scalar or improves_base
        else "Exact-budget surrogate calibration does not improve held-out hard exact-budget capture over the scalar mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_exact_budget_surrogate",
        "selection": selection,
        "hard_rows": hard_rows,
        "diagnosis": {
            "exact_budget_surrogate_closes": closes,
            "selected_source": selected_source,
            "surrogate_hard_mean_capture_ratio": sur["mean_capture_ratio"],
            "surrogate_hard_min_capture_ratio": sur["min_capture_ratio"],
            "scalar_hard_mean_capture_ratio": scalar_summary["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": hard_rows["mechanism_target_ceiling"]["capture"]["summary"]["mean_capture_ratio"],
            "surrogate_improves_scalar": improves_scalar,
            "surrogate_improves_base": improves_base,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "selection_scope": "non-hard eval option_error is used only to fit exact-budget surrogate offsets and select among existing deployable score sources",
            "hard_eval_scope": "held-out hard episodes are used only after surrogate selection",
            "feature_scope": "candidate sources are previously generated non-leaky scalar, set-context, and base predictions; target ceiling is reference-only",
            "deployment": "not deployable policy evidence; this is an exact-budget surrogate transfer audit",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(Path(args.out), **{f"budget_{int(budget)}_score": surrogate[int(budget)].astype(np.float32) for budget in BUDGETS})
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
