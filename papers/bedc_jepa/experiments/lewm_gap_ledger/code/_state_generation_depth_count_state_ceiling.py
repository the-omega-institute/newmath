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
import _state_generation_episode_budget_transfer_audit as budget_audit
import _state_generation_hard_perturbation_value_learner as base_learner


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_depth_count_state_ceiling.json"
DEFAULT_MD = REPORT_DIR / "state_generation_depth_count_state_ceiling.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_depth_count_state_ceiling_predictions.npz"
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


def choice_score(option_error: np.ndarray, depths: np.ndarray, choice: np.ndarray) -> float:
    selected_error = option_error[np.arange(len(choice)), choice.astype(np.int64)]
    selected_depth = depths[choice.astype(np.int64)].astype(np.float64)
    return clean_float(float(np.sum(selected_error) / np.sum(selected_depth)))


def exact_counts(choice: np.ndarray, depths: np.ndarray) -> dict[int, int]:
    out: dict[int, int] = {}
    selected = depths[choice.astype(np.int64)].astype(np.int64)
    for depth in depths.astype(np.int64):
        out[int(depth)] = int(np.sum(selected == int(depth)))
    return out


def count_constrained_choice(score: np.ndarray, depths: np.ndarray, counts: dict[int, int]) -> np.ndarray:
    n = score.shape[0]
    chosen = np.full(n, -1, dtype=np.int64)
    used = np.zeros(n, dtype=bool)
    for depth in sorted(counts):
        k = int(counts[int(depth)])
        if k <= 0:
            continue
        col = int(np.flatnonzero(depths.astype(np.int64) == int(depth))[0])
        local = score[:, col].astype(np.float64).copy()
        local[used] = np.inf
        order = np.argsort(local, kind="mergesort")
        take = order[:k]
        chosen[take] = col
        used[take] = True
    if np.any(chosen < 0):
        fallback_col = int(np.argmin(depths.astype(np.int64)))
        chosen[chosen < 0] = fallback_col
    return chosen.astype(np.int64)


def count_policy_episode_values(
    split: dict[str, np.ndarray],
    score: dict[int, np.ndarray],
    mask: np.ndarray,
    depths: np.ndarray,
    budget: int,
) -> tuple[list[int], np.ndarray, list[dict[str, Any]]]:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    eps: list[int] = []
    values: list[float] = []
    rows: list[dict[str, Any]] = []
    for ep in sorted(int(v) for v in np.unique(episode[mask.astype(bool)])):
        idx = np.flatnonzero((episode == int(ep)) & mask.astype(bool)).astype(np.int64)
        local_error = option_error[idx]
        local_score = score[int(budget)][idx].astype(np.float64)
        oracle_choice = budget_audit.exact_budget_choice_at_multiplier(episode[idx], local_error, depths, int(budget))
        count_state = exact_counts(oracle_choice, depths)
        chosen = count_constrained_choice(local_score, depths, count_state)
        uniform_col = int(np.flatnonzero(depths.astype(np.int64) == int(budget))[0])
        uniform = np.full(len(idx), uniform_col, dtype=np.int64)
        selected_rate = choice_score(local_error, depths, chosen)
        uniform_rate = choice_score(local_error, depths, uniform)
        oracle_rate = choice_score(local_error, depths, oracle_choice)
        values.append(selected_rate - uniform_rate)
        eps.append(int(ep))
        rows.append(
            {
                "episode": int(ep),
                "selected_minus_uniform": clean_float(selected_rate - uniform_rate),
                "oracle_minus_uniform": clean_float(oracle_rate - uniform_rate),
                "regret_to_oracle": clean_float(selected_rate - oracle_rate),
                "oracle_depth_counts": {str(k): int(v) for k, v in count_state.items()},
                "chosen_depth_counts": {str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen], return_counts=True))},
            }
        )
    return eps, np.asarray(values, dtype=np.float64), rows


def capture_summary(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    mask: np.ndarray,
    depths: np.ndarray,
    *,
    seed: int,
    samples: int,
    count_state: bool,
) -> dict[str, Any]:
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget_index, budget in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = candidate_gap.episode_values(split, oracle_score, mask.astype(bool), int(budget))
        if count_state:
            score_eps, score_values, _rows = count_policy_episode_values(split, scores, mask.astype(bool), depths, int(budget))
        else:
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


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Depth-Count State Ceiling",
        "",
        f"- selected source: `{report['diagnosis']['selected_source']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["depth_count_state", "scalar_mechanism", "set_context_mechanism", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit an oracle depth-count state with deployable within-count scores")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--scalar-pred", default=str(SCALAR_PRED))
    parser.add_argument("--set-context-pred", default=str(SET_CONTEXT_PRED))
    parser.add_argument("--base-pred", default=str(BASE_PRED))
    parser.add_argument("--target-pred", default=str(TARGET_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=3011)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    non_hard_mask = ~hard_mask
    scalar = load_scores(Path(args.scalar_pred))
    set_ctx = load_scores(Path(args.set_context_pred))
    base = load_scores(Path(args.base_pred))
    target = load_scores(Path(args.target_pred))
    sources = {
        "scalar_mechanism": scalar,
        "set_context_mechanism": set_ctx,
        "base_perturbation_value": base,
    }
    selection_rows: list[dict[str, Any]] = []
    best_source = "scalar_mechanism"
    best_key = (float("inf"), float("inf"))
    for name, scores in sources.items():
        summary = capture_summary(split, scores, non_hard_mask, depths, seed=int(args.seed), samples=80, count_state=True)["summary"]
        key = (-float(summary["mean_capture_ratio"]), -float(summary["min_capture_ratio"]))
        selection_rows.append({"source": name, **summary, "selection_key": [clean_float(v) for v in key]})
        if key < best_key:
            best_key = key
            best_source = name
    depth_count_scores = sources[best_source]

    hard_rows: dict[str, Any] = {}
    row_specs = {
        "depth_count_state": (depth_count_scores, True),
        "scalar_mechanism": (scalar, False),
        "set_context_mechanism": (set_ctx, False),
        "base_perturbation_value": (base, False),
        "mechanism_target_ceiling": (target, False),
    }
    for index, (name, (scores, count_state)) in enumerate(row_specs.items()):
        hard_rows[name] = {
            "capture": capture_summary(split, scores, hard_mask, depths, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples), count_state=count_state),
            "label_alignment": base_learner.hard_label_alignment(split, depths, BUDGETS, hard_episodes, scores),
        }

    depth_summary = hard_rows["depth_count_state"]["capture"]["summary"]
    scalar_summary = hard_rows["scalar_mechanism"]["capture"]["summary"]
    base_summary = hard_rows["base_perturbation_value"]["capture"]["summary"]
    closes = bool(float(depth_summary["mean_capture_ratio"]) > 0.0 and float(depth_summary["min_capture_ratio"]) > 0.0)
    improves_scalar = bool(float(depth_summary["mean_capture_ratio"]) > float(scalar_summary["mean_capture_ratio"]))
    improves_base = bool(float(depth_summary["mean_capture_ratio"]) > float(base_summary["mean_capture_ratio"]))
    verdict = (
        "Oracle depth-count state with deployable within-count scores closes the held-out hard exact-budget gate on this export; the count state must still be predicted non-leakily."
        if closes
        else "Oracle depth-count state improves the hard mechanism route but does not close all hard exact-budget budgets."
        if improves_scalar or improves_base
        else "Oracle depth-count state does not improve held-out hard exact-budget capture over the scalar mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_depth_count_state_ceiling",
        "selection": selection_rows,
        "hard_rows": hard_rows,
        "diagnosis": {
            "depth_count_state_closes": closes,
            "selected_source": best_source,
            "depth_count_hard_mean_capture_ratio": depth_summary["mean_capture_ratio"],
            "depth_count_hard_min_capture_ratio": depth_summary["min_capture_ratio"],
            "scalar_hard_mean_capture_ratio": scalar_summary["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": hard_rows["mechanism_target_ceiling"]["capture"]["summary"]["mean_capture_ratio"],
            "depth_count_improves_scalar": improves_scalar,
            "depth_count_improves_base": improves_base,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "selection_scope": "non-hard eval option_error is used only to choose the deployable within-count score source under an oracle depth-count state",
            "hard_eval_scope": "held-out hard option_error constructs oracle depth counts and evaluates final capture; this is a ceiling audit, not deployable policy evidence",
            "feature_scope": "within-count scores are previously generated non-leaky scalar, set-context, and base predictions; target ceiling is reference-only",
            "deployment": "not deployable because hard oracle depth-count state is supplied at evaluation",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy", "non-leaky count-state predictor", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(Path(args.out), **{f"budget_{int(budget)}_score": depth_count_scores[int(budget)].astype(np.float32) for budget in BUDGETS})
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps({"status": "ok", "diagnosis": report["diagnosis"]}, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
