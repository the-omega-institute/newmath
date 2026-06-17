from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_assignment_bottleneck_learner as bottleneck
import _state_generation_budget_conditioned_assignment_bottleneck as budget_bottleneck
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_assignment_state_recoverability.json"
DEFAULT_MD = REPORT_DIR / "state_generation_assignment_state_recoverability.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_assignment_state_recoverability_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BUDGETS = bottleneck.BUDGETS


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


def shuffle_scores_by_episode(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    *,
    seed: int,
) -> dict[int, np.ndarray]:
    episode = split["episode"].astype(np.int64)
    unique = np.unique(episode)
    rng = np.random.default_rng(seed)
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        shuffled = np.empty_like(scores[int(budget)].astype(np.float64))
        perm = rng.permutation(unique)
        for dst_ep, src_ep in zip(unique, perm, strict=True):
            dst = np.flatnonzero(episode == int(dst_ep)).astype(np.int64)
            src = np.flatnonzero(episode == int(src_ep)).astype(np.int64)
            local = scores[int(budget)][src].astype(np.float64)
            if len(local) < len(dst):
                reps = int(np.ceil(len(dst) / max(len(local), 1)))
                local = np.tile(local, (reps, 1))
            shuffled[dst] = local[: len(dst)]
        out[int(budget)] = shuffled.astype(np.float64)
    return out


def append_state(
    base_design: dict[int, np.ndarray],
    split: dict[str, np.ndarray],
    state_scores: dict[int, np.ndarray],
) -> dict[int, np.ndarray]:
    return {
        int(budget): np.concatenate(
            [base_design[int(budget)], bottleneck.episode_state_features(split, state_scores, int(budget))],
            axis=1,
        ).astype(np.float64)
        for budget in BUDGETS.astype(np.int64)
    }


def train_and_apply(
    train_design: dict[int, np.ndarray],
    train_targets: dict[int, np.ndarray],
    cal_design: dict[int, np.ndarray],
    cal_split: dict[str, np.ndarray],
    eval_design: dict[int, np.ndarray],
    shape: tuple[int, int],
) -> tuple[dict[int, np.ndarray], dict[str, Any]]:
    models, selection = budget_bottleneck.select_budget_models(
        train_design,
        train_targets,
        cal_design,
        cal_split,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    return budget_bottleneck.apply_budget_models(eval_design, models, shape), {"selection": selection, "models": models}


def exact_budget_cardinality_audit(
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    hard_episodes: list[int],
    score_rows: dict[str, dict[int, np.ndarray]],
) -> dict[str, Any]:
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    episode = split["episode"].astype(np.int64)[hard_mask]
    out: dict[str, Any] = {}
    for name, scores in score_rows.items():
        row: dict[str, Any] = {}
        rates: list[float] = []
        for budget in BUDGETS.astype(np.int64):
            chosen = budget_audit.exact_budget_choice_at_multiplier(
                episode,
                scores[int(budget)][hard_mask].astype(np.float64),
                depths,
                int(budget),
            )
            passed = 0
            total = 0
            for ep in np.unique(episode):
                idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
                selected_sum = int(np.sum(depths[chosen[idx]].astype(np.int64)))
                target_sum = int(budget) * len(idx)
                total += 1
                if selected_sum == target_sum:
                    passed += 1
            rate = float(passed) / float(max(total, 1))
            rates.append(rate)
            row[f"budget_{int(budget)}"] = {"exact_cardinality_rate": clean_float(rate), "episodes": int(total)}
        row["all_exact"] = bool(all(rate == 1.0 for rate in rates))
        out[name] = row
    out["all_rows_exact"] = bool(all(row.get("all_exact") is True for row in out.values() if isinstance(row, dict)))
    return out


def label_prediction_audit(
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    hard_episodes: list[int],
    real_scores: dict[int, np.ndarray],
    control_scores: dict[str, dict[int, np.ndarray]],
    *,
    epsilon: float,
) -> dict[str, Any]:
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    hard_split = {k: v[hard_mask] for k, v in split.items()}
    targets = bottleneck.base_learner.forced_delta_targets(hard_split, depths, BUDGETS)
    rows: dict[str, Any] = {}
    noninferior: list[bool] = []
    real_advantage: list[bool] = []
    for name, scores in control_scores.items():
        budget_rows: dict[str, Any] = {}
        ratios: list[float] = []
        for budget in BUDGETS.astype(np.int64):
            y = targets[int(budget)].reshape(-1).astype(np.float64)
            real = real_scores[int(budget)][hard_mask].reshape(-1).astype(np.float64)
            ctrl = scores[int(budget)][hard_mask].reshape(-1).astype(np.float64)
            real_mse = float(np.mean((real - y) ** 2))
            ctrl_mse = float(np.mean((ctrl - y) ** 2))
            ratio = real_mse / max(ctrl_mse, 1.0e-12)
            ratios.append(ratio)
            ni = bool(ratio <= 1.0 + float(epsilon))
            adv = bool(ratio < 1.0 - float(epsilon))
            noninferior.append(ni)
            real_advantage.append(adv)
            budget_rows[f"budget_{int(budget)}"] = {
                "real_assignment_state_mse": clean_float(real_mse),
                "control_mse": clean_float(ctrl_mse),
                "mse_ratio_real_over_control": clean_float(ratio),
                "real_noninferior_to_control": ni,
                "material_real_prediction_advantage": adv,
            }
        rows[name] = {
            "budget_rows": budget_rows,
            "mean_mse_ratio_real_over_control": clean_float(float(np.mean(ratios))),
        }
    return {
        "metric": "forced_delta_assignment_label_prediction_parity",
        "epsilon": clean_float(float(epsilon)),
        "rows": rows,
        "real_noninferior_to_all_controls": bool(all(noninferior)),
        "material_real_prediction_advantage_against_any_control": bool(any(real_advantage)),
        "scope": "Matched forced-delta assignment-label audit only; not LeWorldModel next-latent prediction parity.",
    }


def hard_rows(
    eval_split: dict[str, np.ndarray],
    depths: np.ndarray,
    hard_episodes: list[int],
    scores: dict[str, dict[int, np.ndarray]],
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    rows: dict[str, Any] = {}
    for index, (name, score) in enumerate(scores.items()):
        rows[name] = {
            "capture": bottleneck.capture_summary(eval_split, score, mask, seed=seed + 1000 * index, samples=samples),
            "label_alignment": bottleneck.label_alignment(eval_split, depths, hard_episodes, score),
        }
    return rows


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Assignment-State Recoverability",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in [
        "real_assignment_state",
        "shuffled_assignment_state",
        "no_assignment_control",
        "swapped_assignment_state",
        "mechanism_target_ceiling",
    ]:
        row = report["hard_rows"][name]
        summary = row["capture"]["summary"]
        rho = row["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {summary['mean_capture_ratio']:.6g} | {summary['budget2_capture_ratio']:.6g} | "
            f"{summary['budget3_capture_ratio']:.6g} | {summary['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    d = report["diagnosis"]
    lines.extend(
        [
            "",
            "## Gates",
            "",
            f"- exact-budget cardinality: `{report['exact_budget_cardinality_audit']['all_rows_exact']}`",
            f"- real beats shuffled capture: `{d['real_beats_shuffled_capture']}`",
            f"- real beats no-assignment capture: `{d['real_beats_no_assignment_capture']}`",
            f"- real beats shuffled label rho: `{d['real_beats_shuffled_label_rho']}`",
            f"- label prediction noninferior to controls: `{report['label_prediction_audit']['real_noninferior_to_all_controls']}`",
            "",
            "## Verdict",
            "",
            report["verdict"],
        ]
    )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Assignment-state recoverability diagnostic with shuffled and no-assignment controls")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=6102)
    parser.add_argument("--projection-width", type=int, default=160)
    parser.add_argument("--bootstrap-samples", type=int, default=160)
    parser.add_argument("--parity-epsilon", type=float, default=0.05)
    args = parser.parse_args()

    data = bottleneck.load_npz(Path(args.export))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    mean, scale = bottleneck.fit_standardizer(data["train_x"])
    proj = bottleneck.random_projection(data["train_x"].shape[1], int(args.projection_width), int(args.seed))
    train_proj = bottleneck.split_projected(data, "train", mean, scale, proj)
    cal_proj = bottleneck.split_projected(data, "calibration", mean, scale, proj)
    eval_proj = bottleneck.split_projected(data, "eval", mean, scale, proj)
    train_base = bottleneck.design_by_budget(train_proj, depths, BUDGETS)
    cal_base = bottleneck.design_by_budget(cal_proj, depths, BUDGETS)
    eval_base = bottleneck.design_by_budget(eval_proj, depths, BUDGETS)
    train_targets = bottleneck.base_learner.forced_delta_targets(train, depths, BUDGETS)

    stage_models, stage_selection = budget_bottleneck.select_budget_models(
        train_base,
        train_targets,
        cal_base,
        cal,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    train_stage = budget_bottleneck.apply_budget_models(train_base, stage_models, train["option_error"].shape)
    cal_stage = budget_bottleneck.apply_budget_models(cal_base, stage_models, cal["option_error"].shape)
    eval_stage = budget_bottleneck.apply_budget_models(eval_base, stage_models, eval_split["option_error"].shape)
    train_shuffled_stage = shuffle_scores_by_episode(train, train_stage, seed=int(args.seed) + 11)
    cal_shuffled_stage = shuffle_scores_by_episode(cal, cal_stage, seed=int(args.seed) + 13)
    eval_shuffled_stage = shuffle_scores_by_episode(eval_split, eval_stage, seed=int(args.seed) + 17)

    train_real = append_state(train_base, train, train_stage)
    cal_real = append_state(cal_base, cal, cal_stage)
    eval_real = append_state(eval_base, eval_split, eval_stage)
    train_shuffled = append_state(train_base, train, train_shuffled_stage)
    cal_shuffled = append_state(cal_base, cal, cal_shuffled_stage)
    eval_shuffled = append_state(eval_base, eval_split, eval_shuffled_stage)
    train_no_assignment = bottleneck.control_design(train_base, train_proj, train, depths)
    cal_no_assignment = bottleneck.control_design(cal_base, cal_proj, cal, depths)
    eval_no_assignment = bottleneck.control_design(eval_base, eval_proj, eval_split, depths)

    real_scores, real_fit = train_and_apply(train_real, train_targets, cal_real, cal, eval_real, eval_split["option_error"].shape)
    shuffled_scores, shuffled_fit = train_and_apply(
        train_shuffled,
        train_targets,
        cal_shuffled,
        cal,
        eval_shuffled,
        eval_split["option_error"].shape,
    )
    no_assignment_scores, no_assignment_fit = train_and_apply(
        train_no_assignment,
        train_targets,
        cal_no_assignment,
        cal,
        eval_no_assignment,
        eval_split["option_error"].shape,
    )
    swapped_scores = budget_bottleneck.apply_budget_models(eval_shuffled, real_fit["models"], eval_split["option_error"].shape)
    target_scores = bottleneck.base_learner.forced_delta_targets(eval_split, depths, BUDGETS)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    score_rows = {
        "real_assignment_state": real_scores,
        "shuffled_assignment_state": shuffled_scores,
        "no_assignment_control": no_assignment_scores,
        "swapped_assignment_state": swapped_scores,
        "mechanism_target_ceiling": target_scores,
    }
    rows = hard_rows(
        eval_split,
        depths,
        hard_episodes,
        score_rows,
        seed=int(args.seed),
        samples=int(args.bootstrap_samples),
    )
    exact_audit = exact_budget_cardinality_audit(eval_split, depths, hard_episodes, score_rows)
    parity_audit = label_prediction_audit(
        eval_split,
        depths,
        hard_episodes,
        real_scores,
        {
            "shuffled_assignment_state": shuffled_scores,
            "no_assignment_control": no_assignment_scores,
        },
        epsilon=float(args.parity_epsilon),
    )

    real_summary = rows["real_assignment_state"]["capture"]["summary"]
    shuffled_summary = rows["shuffled_assignment_state"]["capture"]["summary"]
    no_summary = rows["no_assignment_control"]["capture"]["summary"]
    swapped_summary = rows["swapped_assignment_state"]["capture"]["summary"]
    target_summary = rows["mechanism_target_ceiling"]["capture"]["summary"]
    real_rho = float(rows["real_assignment_state"]["label_alignment"]["mean_score_label_spearman"])
    shuffled_rho = float(rows["shuffled_assignment_state"]["label_alignment"]["mean_score_label_spearman"])
    no_rho = float(rows["no_assignment_control"]["label_alignment"]["mean_score_label_spearman"])
    closes = bool(float(real_summary["mean_capture_ratio"]) > 0.0 and float(real_summary["min_capture_ratio"]) > 0.0)
    beats_shuffled_capture = bool(float(real_summary["mean_capture_ratio"]) > float(shuffled_summary["mean_capture_ratio"]))
    beats_no_capture = bool(float(real_summary["mean_capture_ratio"]) > float(no_summary["mean_capture_ratio"]))
    beats_shuffled_rho = bool(real_rho > shuffled_rho)
    beats_no_rho = bool(real_rho > no_rho)
    swap_sensitive = bool(float(real_summary["mean_capture_ratio"]) > float(swapped_summary["mean_capture_ratio"]))
    valid = bool(
        exact_audit["all_rows_exact"]
        and beats_shuffled_capture
        and beats_no_capture
        and beats_shuffled_rho
        and beats_no_rho
        and parity_audit["real_noninferior_to_all_controls"]
    )
    if closes and valid:
        verdict = (
            "The assignment-state recoverability diagnostic closes this learner gate on the held-out hard slice; "
            "LeWorldModel next-latent parity and independent export validation remain required."
        )
    elif valid:
        verdict = (
            "The real assignment-state channel beats shuffled and no-assignment controls on this diagnostic, "
            "but the all-budget hard allocation gate remains open."
        )
    else:
        verdict = "The real assignment-state channel does not pass the matched shuffled/no-assignment recoverability gate."

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_assignment_state_recoverability",
        "feature_dims": {
            "projection_width": int(args.projection_width),
            "base_design": int(next(iter(train_base.values())).shape[1]),
            "assignment_state_design": int(next(iter(train_real.values())).shape[1]),
            "no_assignment_design": int(next(iter(train_no_assignment.values())).shape[1]),
        },
        "selection": {
            "stage": stage_selection,
            "real_assignment_state": real_fit["selection"],
            "shuffled_assignment_state": shuffled_fit["selection"],
            "no_assignment_control": no_assignment_fit["selection"],
        },
        "hard_rows": rows,
        "exact_budget_cardinality_audit": exact_audit,
        "label_prediction_audit": parity_audit,
        "diagnosis": {
            "assignment_state_recoverability_valid": valid,
            "assignment_state_recoverability_closes": closes,
            "real_hard_mean_capture_ratio": real_summary["mean_capture_ratio"],
            "real_hard_min_capture_ratio": real_summary["min_capture_ratio"],
            "shuffled_hard_mean_capture_ratio": shuffled_summary["mean_capture_ratio"],
            "no_assignment_hard_mean_capture_ratio": no_summary["mean_capture_ratio"],
            "swapped_hard_mean_capture_ratio": swapped_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": target_summary["mean_capture_ratio"],
            "real_minus_shuffled_mean_capture": clean_float(float(real_summary["mean_capture_ratio"]) - float(shuffled_summary["mean_capture_ratio"])),
            "real_minus_no_assignment_mean_capture": clean_float(float(real_summary["mean_capture_ratio"]) - float(no_summary["mean_capture_ratio"])),
            "real_minus_swapped_mean_capture": clean_float(float(real_summary["mean_capture_ratio"]) - float(swapped_summary["mean_capture_ratio"])),
            "real_hard_label_rho": clean_float(real_rho),
            "shuffled_hard_label_rho": clean_float(shuffled_rho),
            "no_assignment_hard_label_rho": clean_float(no_rho),
            "real_beats_shuffled_capture": beats_shuffled_capture,
            "real_beats_no_assignment_capture": beats_no_capture,
            "real_beats_shuffled_label_rho": beats_shuffled_rho,
            "real_beats_no_assignment_label_rho": beats_no_rho,
            "swap_sensitive": swap_sensitive,
            "exact_budget_cardinality_passed": bool(exact_audit["all_rows_exact"]),
            "label_prediction_noninferior_to_controls": bool(parity_audit["real_noninferior_to_all_controls"]),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "all learner arms use train-standardized latent-action projections and deployable score-state summaries; eval option_error is not a feature",
            "assignment_channel": "the real channel uses train/cal learned forced-delta score summaries; the shuffled channel preserves dimensions and score marginals while permuting episode assignment linkage",
            "labels": "train option_error constructs forced-delta assignment labels for supervised training; calibration option_error is used only for model selection",
            "final_eval": "held-out hard eval episodes are used only after stage and final model selection",
            "matched_controls": "shuffled and no-assignment controls share target labels, budgets, ridge family, lambda grid, calibration rule, and per-budget training schedule",
            "oracle_scope": "mechanism target ceiling is reported only as a reference and is not an inference-time feature",
        },
        "not_claimed": [
            "LeWorldModel next-latent prediction parity",
            "deployable policy beyond this export",
            "independent export validation",
            "complete BEDC-native world model",
            "allocation closure unless mean and all-budget hard capture are positive",
        ],
    }
    np.savez_compressed(
        Path(args.out),
        **{f"budget_{int(budget)}_score": real_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
        **{f"shuffled_budget_{int(budget)}_score": shuffled_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
        **{f"no_assignment_budget_{int(budget)}_score": no_assignment_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
        **{f"swapped_budget_{int(budget)}_score": swapped_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"status": "ok", "diagnosis": report["diagnosis"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
