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
import _state_generation_hard_perturbation_value_learner as learner


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_mechanism_aware_assignment_target.json"
DEFAULT_MD = REPORT_DIR / "state_generation_mechanism_aware_assignment_target.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_mechanism_aware_assignment_target_predictions.npz"
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


def mechanism_labels(split: dict[str, np.ndarray], depths: np.ndarray, budgets: np.ndarray) -> dict[int, np.ndarray]:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    out = {int(budget): np.zeros_like(option_error, dtype=np.float64) for budget in budgets.astype(np.int64)}
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        local = option_error[idx]
        for budget in budgets.astype(np.int64):
            out[int(budget)][idx] = hard_value.forced_delta_labels(local, depths, int(budget) * len(idx))
    return out


def zscore_like(reference: np.ndarray, value: np.ndarray) -> np.ndarray:
    mean = float(np.mean(reference.astype(np.float64)))
    scale = float(np.std(reference.astype(np.float64)))
    if scale < 1.0e-6:
        scale = 1.0
    return ((value.astype(np.float64) - mean) / scale).astype(np.float64)


def candidate_scores(
    split: dict[str, np.ndarray],
    learner_scores: dict[int, np.ndarray],
    labels: dict[int, np.ndarray],
) -> dict[str, dict[int, np.ndarray]]:
    option_error = split["option_error"].astype(np.float64)
    out: dict[str, dict[int, np.ndarray]] = {
        "oracle_option_error": {int(budget): option_error for budget in BUDGETS},
        "mechanism_forced_delta": {int(budget): labels[int(budget)] for budget in BUDGETS},
        "learner_base": learner_scores,
    }
    for lam in (0.10, 0.25, 0.50, 0.75, 1.00, 1.50, 2.00):
        out[f"learner_plus_mechanism_{lam:.2f}"] = {}
        out[f"oracle_plus_mechanism_{lam:.2f}"] = {}
        for budget in BUDGETS.astype(np.int64):
            label_z = zscore_like(labels[int(budget)], labels[int(budget)])
            learner_z = zscore_like(learner_scores[int(budget)], learner_scores[int(budget)])
            error_z = zscore_like(option_error, option_error)
            out[f"learner_plus_mechanism_{lam:.2f}"][int(budget)] = learner_z + float(lam) * label_z
            out[f"oracle_plus_mechanism_{lam:.2f}"][int(budget)] = error_z + float(lam) * label_z
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
    return learner.hard_label_alignment(split, depths, BUDGETS, hard_episodes, scores)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Mechanism-Aware Assignment Target",
        "",
        f"- selected non-hard target: `{report['diagnosis']['selected_candidate']}`",
        f"- candidate count: `{report['candidate_count']}`",
        "",
        "| target | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard regret | hard label rho |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for name in ["selected", "learner_base", "mechanism_forced_delta", "oracle_option_error"]:
        payload = report["hard_rows"][name]
        row = payload["summary"]
        rho = payload["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | "
            f"{row['mean_regret_to_oracle']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit mechanism-aware exact-budget assignment targets")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--learner-pred", default=str(LEARNER_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2221)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    non_hard_mask = ~hard_mask
    pred = load_npz(Path(args.learner_pred))
    learner_scores = {int(budget): pred[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    labels = mechanism_labels(split, depths, BUDGETS)
    candidates = candidate_scores(split, learner_scores, labels)
    ranking: list[dict[str, Any]] = []
    for name, scores in sorted(candidates.items()):
        non_summary = global_transfer.observed_summary(split, scores, non_hard_mask)
        ranking.append({"candidate": name, **non_summary})
    ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    selected = str(ranking[0]["candidate"])
    selected_scores = candidates[selected]
    hard_rows: dict[str, Any] = {}
    row_sources = {
        "selected": selected_scores,
        "learner_base": candidates["learner_base"],
        "mechanism_forced_delta": candidates["mechanism_forced_delta"],
        "oracle_option_error": candidates["oracle_option_error"],
    }
    for index, (name, scores) in enumerate(row_sources.items()):
        row = summarize_candidate(split, scores, hard_mask, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples))
        row["label_alignment"] = label_alignment(split, depths, hard_episodes, scores)
        hard_rows[name] = row
    selected_non_hard = summarize_candidate(split, selected_scores, non_hard_mask, seed=int(args.seed) + 7000, samples=int(args.bootstrap_samples))
    target_closes = bool(
        float(hard_rows["mechanism_forced_delta"]["summary"]["mean_capture_ratio"]) > 0.0
        and float(hard_rows["mechanism_forced_delta"]["summary"]["min_capture_ratio"]) > 0.0
    )
    selected_transfers = bool(
        float(hard_rows["selected"]["summary"]["mean_capture_ratio"]) > float(hard_rows["learner_base"]["summary"]["mean_capture_ratio"])
    )
    verdict = (
        "Mechanism-aware forced-delta assignment target closes the hard exact-budget target gate, but non-hard target selection still must transfer before deployable allocation can be claimed."
        if target_closes and not selected_transfers
        else "Mechanism-aware target selection transfers to hard episodes and improves over the base perturbation-value learner on this export; independent validation is required."
        if selected_transfers
        else "Mechanism-aware target selection does not improve hard transfer over the base perturbation-value learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_mechanism_aware_assignment_target",
        "candidate_count": int(len(candidates)),
        "selection_non_hard": selected_non_hard,
        "hard_rows": hard_rows,
        "ranking": ranking[:12],
        "diagnosis": {
            "selected_candidate": selected,
            "mechanism_target_hard_closes": target_closes,
            "selected_transfers_over_base": selected_transfers,
            "selected_hard_mean_capture_ratio": hard_rows["selected"]["summary"]["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": hard_rows["learner_base"]["summary"]["mean_capture_ratio"],
            "mechanism_target_hard_mean_capture_ratio": hard_rows["mechanism_forced_delta"]["summary"]["mean_capture_ratio"],
            "oracle_hard_mean_capture_ratio": hard_rows["oracle_option_error"]["summary"]["mean_capture_ratio"],
        },
        "verdict": verdict,
        "leakage_attestation": {
            "oracle_scope": "eval option_error constructs diagnostic mechanism targets and oracle reference rows; this is a target audit, not deployable training",
            "selection": "candidate selection uses non-hard eval episodes; held-out hard episodes are used only for target transfer evaluation",
            "training": "no model training is performed",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
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
