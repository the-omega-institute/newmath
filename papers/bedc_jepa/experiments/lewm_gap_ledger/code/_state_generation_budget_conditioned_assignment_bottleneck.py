from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_assignment_bottleneck_learner as base
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_budget_conditioned_assignment_bottleneck.json"
DEFAULT_MD = REPORT_DIR / "state_generation_budget_conditioned_assignment_bottleneck.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_budget_conditioned_assignment_bottleneck_predictions.npz"
DEFAULT_BASELINE = REPORT_DIR / "state_generation_assignment_bottleneck_learner.json"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BUDGETS = base.BUDGETS


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


def apply_single_ridge(design: np.ndarray, model: dict[str, np.ndarray], shape: tuple[int, int]) -> np.ndarray:
    z = base.apply_standardizer(design, model["mean"], model["scale"])
    aug = np.concatenate([z, np.ones((len(z), 1), dtype=np.float64)], axis=1)
    return (aug @ model["beta"]).reshape(shape).astype(np.float64)


def single_budget_capture(
    split: dict[str, np.ndarray],
    scores: np.ndarray,
    budget: int,
    mask: np.ndarray,
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    oracle_eps, oracle_values = base.oracle_gap.episode_values(split, split["option_error"].astype(np.float64), mask.astype(bool), int(budget))
    score_eps, score_values = base.oracle_gap.episode_values(split, scores.astype(np.float64), mask.astype(bool), int(budget))
    if oracle_eps != score_eps:
        raise ValueError(f"episode mismatch for budget {budget}")
    regret = score_values - oracle_values
    oracle_mean = float(np.mean(oracle_values))
    score_mean = float(np.mean(score_values))
    capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
    return {
        "score_delta": base.oracle_gap.bootstrap_mean(score_values, seed=seed, samples=samples),
        "oracle_delta": base.oracle_gap.bootstrap_mean(oracle_values, seed=seed + 17, samples=samples),
        "regret_to_oracle": base.oracle_gap.bootstrap_mean(regret, seed=seed + 31, samples=samples),
        "headroom_capture_ratio": clean_float(float(capture)),
        "mean_regret_to_oracle": clean_float(float(np.mean(regret))),
    }


def select_budget_model(
    train_design: dict[int, np.ndarray],
    train_targets: dict[int, np.ndarray],
    cal_design: dict[int, np.ndarray],
    cal_split: dict[str, np.ndarray],
    budget: int,
    *,
    lambdas: tuple[float, ...],
) -> tuple[dict[str, np.ndarray], list[dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    best_key = (float("inf"), float("inf"))
    best_model: dict[str, np.ndarray] | None = None
    cal_mask = np.ones(len(cal_split["episode"]), dtype=bool)
    for lam in lambdas:
        model = base.fit_ridge(train_design[int(budget)], train_targets[int(budget)].reshape(-1), float(lam))
        cal_scores = apply_single_ridge(cal_design[int(budget)], model, cal_split["option_error"].shape)
        summary = single_budget_capture(cal_split, cal_scores, int(budget), cal_mask, seed=6901 + int(budget) * 101 + int(lam), samples=80)
        key = (-float(summary["headroom_capture_ratio"]), float(summary["mean_regret_to_oracle"]))
        rows.append(
            {
                "budget": int(budget),
                "lambda": clean_float(float(lam)),
                "selection_key": [clean_float(v) for v in key],
                "headroom_capture_ratio": summary["headroom_capture_ratio"],
                "mean_regret_to_oracle": summary["mean_regret_to_oracle"],
            }
        )
        if key < best_key:
            best_key = key
            best_model = model
    if best_model is None:
        raise RuntimeError(f"no budget model selected for budget {budget}")
    return best_model, rows


def select_budget_models(
    train_design: dict[int, np.ndarray],
    train_targets: dict[int, np.ndarray],
    cal_design: dict[int, np.ndarray],
    cal_split: dict[str, np.ndarray],
    *,
    lambdas: tuple[float, ...],
) -> tuple[dict[int, dict[str, np.ndarray]], dict[str, Any]]:
    models: dict[int, dict[str, np.ndarray]] = {}
    rows: dict[str, Any] = {}
    for budget in BUDGETS.astype(np.int64):
        model, selection = select_budget_model(
            train_design,
            train_targets,
            cal_design,
            cal_split,
            int(budget),
            lambdas=lambdas,
        )
        models[int(budget)] = model
        rows[f"budget_{int(budget)}"] = selection
    return models, rows


def apply_budget_models(
    designs: dict[int, np.ndarray],
    models: dict[int, dict[str, np.ndarray]],
    shape: tuple[int, int],
) -> dict[int, np.ndarray]:
    return {
        int(budget): apply_single_ridge(designs[int(budget)], models[int(budget)], shape)
        for budget in BUDGETS.astype(np.int64)
    }


def budget_prediction_audit(
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    hard_episodes: list[int],
    bottleneck_scores: dict[int, np.ndarray],
    control_scores: dict[int, np.ndarray],
    *,
    epsilon: float,
) -> dict[str, Any]:
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    hard_split = {k: v[hard_mask] for k, v in split.items()}
    targets = base.base_learner.forced_delta_targets(hard_split, depths, BUDGETS)
    rows: dict[str, Any] = {}
    ratios: list[float] = []
    for budget in BUDGETS.astype(np.int64):
        b_score = bottleneck_scores[int(budget)][hard_mask].reshape(-1).astype(np.float64)
        c_score = control_scores[int(budget)][hard_mask].reshape(-1).astype(np.float64)
        y = targets[int(budget)].reshape(-1).astype(np.float64)
        b_mse = float(np.mean((b_score - y) ** 2))
        c_mse = float(np.mean((c_score - y) ** 2))
        ratio = b_mse / max(c_mse, 1.0e-12)
        ratios.append(float(ratio))
        rows[f"budget_{int(budget)}"] = {
            "assignment_bottleneck_label_mse": clean_float(b_mse),
            "matched_control_label_mse": clean_float(c_mse),
            "mse_ratio_bottleneck_over_control": clean_float(ratio),
            "noninferior_to_control": bool(ratio <= 1.0 + float(epsilon)),
            "material_prediction_advantage": bool(ratio < 1.0 - float(epsilon)),
        }
    mean_ratio = float(np.mean(ratios))
    return {
        "metric": "forced_delta_label_prediction_parity",
        "epsilon": clean_float(float(epsilon)),
        "rows": rows,
        "mean_mse_ratio_bottleneck_over_control": clean_float(mean_ratio),
        "prediction_parity_checked": True,
        "noninferior_to_control": bool(all(row["noninferior_to_control"] for row in rows.values())),
        "material_prediction_advantage": bool(any(row["material_prediction_advantage"] for row in rows.values())),
        "scope": "This is a matched forced-delta label prediction audit, not LeWorldModel next-latent prediction parity.",
    }


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
        all_rates: list[float] = []
        for budget in BUDGETS.astype(np.int64):
            local_score = scores[int(budget)][hard_mask].astype(np.float64)
            chosen = budget_audit.exact_budget_choice_at_multiplier(episode, local_score, depths, int(budget))
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
            all_rates.append(rate)
            row[f"budget_{int(budget)}"] = {
                "exact_cardinality_rate": clean_float(rate),
                "episodes": int(total),
            }
        row["all_exact"] = bool(all(rate == 1.0 for rate in all_rates))
        out[name] = row
    out["all_rows_exact"] = bool(all(row.get("all_exact") is True for row in out.values() if isinstance(row, dict)))
    return out


def hard_capture_rows(
    eval_split: dict[str, np.ndarray],
    depths: np.ndarray,
    hard_episodes: list[int],
    score_rows: dict[str, dict[int, np.ndarray]],
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(score_rows.items()):
        rows[name] = {
            "capture": base.capture_summary(eval_split, scores, hard_mask, seed=seed + 1000 * index, samples=samples),
            "label_alignment": base.label_alignment(eval_split, depths, hard_episodes, scores),
        }
    return rows


def load_baseline(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"available": False}
    report = json.loads(path.read_text(encoding="utf-8"))
    diagnosis = report.get("diagnosis", {}) if isinstance(report.get("diagnosis"), dict) else {}
    return {
        "available": True,
        "bottleneck_hard_mean_capture_ratio": diagnosis.get("bottleneck_hard_mean_capture_ratio"),
        "control_hard_mean_capture_ratio": diagnosis.get("control_hard_mean_capture_ratio"),
        "bottleneck_minus_control_mean_capture": diagnosis.get("bottleneck_minus_control_mean_capture"),
        "prediction_parity_checked": diagnosis.get("prediction_parity_checked", False),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Budget-Conditioned Assignment Bottleneck",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in [
        "budget_conditioned_assignment_bottleneck",
        "budget_conditioned_nonmechanism_control",
        "mechanism_target_ceiling",
    ]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    audit = report["prediction_parity_audit"]
    lines.extend(
        [
            "",
            "## Gates",
            "",
            f"- exact-budget cardinality: `{report['exact_budget_cardinality_audit']['all_rows_exact']}`",
            f"- forced-delta label prediction parity checked: `{audit['prediction_parity_checked']}`",
            f"- bottleneck/control mean MSE ratio: `{audit['mean_mse_ratio_bottleneck_over_control']:.6g}`",
            f"- material prediction advantage: `{audit['material_prediction_advantage']}`",
            "",
            "## Verdict",
            "",
            report["verdict"],
        ]
    )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Budget-specific non-leaky assignment bottleneck diagnostic")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--baseline", default=str(DEFAULT_BASELINE))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=5101)
    parser.add_argument("--projection-width", type=int, default=160)
    parser.add_argument("--bootstrap-samples", type=int, default=160)
    parser.add_argument("--parity-epsilon", type=float, default=0.05)
    args = parser.parse_args()

    data = base.load_npz(Path(args.export))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    mean, scale = base.fit_standardizer(data["train_x"])
    proj = base.random_projection(data["train_x"].shape[1], int(args.projection_width), int(args.seed))
    train_proj = base.split_projected(data, "train", mean, scale, proj)
    cal_proj = base.split_projected(data, "calibration", mean, scale, proj)
    eval_proj = base.split_projected(data, "eval", mean, scale, proj)
    train_base = base.design_by_budget(train_proj, depths, BUDGETS)
    cal_base = base.design_by_budget(cal_proj, depths, BUDGETS)
    eval_base = base.design_by_budget(eval_proj, depths, BUDGETS)
    train_targets = base.base_learner.forced_delta_targets(train, depths, BUDGETS)

    stage_models, stage_selection = select_budget_models(
        train_base,
        train_targets,
        cal_base,
        cal,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    train_stage = apply_budget_models(train_base, stage_models, train["option_error"].shape)
    cal_stage = apply_budget_models(cal_base, stage_models, cal["option_error"].shape)
    eval_stage = apply_budget_models(eval_base, stage_models, eval_split["option_error"].shape)

    train_bottleneck = base.bottleneck_design(train_base, train, train_stage)
    cal_bottleneck = base.bottleneck_design(cal_base, cal, cal_stage)
    eval_bottleneck = base.bottleneck_design(eval_base, eval_split, eval_stage)
    train_control = base.control_design(train_base, train_proj, train, depths)
    cal_control = base.control_design(cal_base, cal_proj, cal, depths)
    eval_control = base.control_design(eval_base, eval_proj, eval_split, depths)

    bottleneck_models, bottleneck_selection = select_budget_models(
        train_bottleneck,
        train_targets,
        cal_bottleneck,
        cal,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    control_models, control_selection = select_budget_models(
        train_control,
        train_targets,
        cal_control,
        cal,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    bottleneck_scores = apply_budget_models(eval_bottleneck, bottleneck_models, eval_split["option_error"].shape)
    control_scores = apply_budget_models(eval_control, control_models, eval_split["option_error"].shape)
    target_scores = base.base_learner.forced_delta_targets(eval_split, depths, BUDGETS)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))

    score_rows = {
        "budget_conditioned_assignment_bottleneck": bottleneck_scores,
        "budget_conditioned_nonmechanism_control": control_scores,
        "mechanism_target_ceiling": target_scores,
    }
    hard_rows = hard_capture_rows(
        eval_split,
        depths,
        hard_episodes,
        score_rows,
        seed=int(args.seed),
        samples=int(args.bootstrap_samples),
    )
    parity_audit = budget_prediction_audit(
        eval_split,
        depths,
        hard_episodes,
        bottleneck_scores,
        control_scores,
        epsilon=float(args.parity_epsilon),
    )
    exact_audit = exact_budget_cardinality_audit(eval_split, depths, hard_episodes, score_rows)

    bottleneck_summary = hard_rows["budget_conditioned_assignment_bottleneck"]["capture"]["summary"]
    control_summary = hard_rows["budget_conditioned_nonmechanism_control"]["capture"]["summary"]
    target_summary = hard_rows["mechanism_target_ceiling"]["capture"]["summary"]
    delta = float(bottleneck_summary["mean_capture_ratio"]) - float(control_summary["mean_capture_ratio"])
    closes = bool(float(bottleneck_summary["mean_capture_ratio"]) > 0.0 and float(bottleneck_summary["min_capture_ratio"]) > 0.0)
    beats_control = bool(delta > 0.0)
    at_least_one_positive = bool(
        any(float(bottleneck_summary[f"budget{int(budget)}_capture_ratio"]) > 0.0 for budget in BUDGETS.astype(np.int64))
    )
    if closes and beats_control and parity_audit["noninferior_to_control"] and exact_audit["all_rows_exact"]:
        verdict = (
            "Budget-specific assignment-bottleneck training closes the hard all-budget learner gate on this export; "
            "LeWorldModel prediction parity and independent export validation remain required before a world-model claim."
        )
    elif beats_control:
        verdict = (
            "Budget-specific assignment-bottleneck training beats the matched budget-conditioned non-mechanism control, "
            "but the hard all-budget gate remains open."
        )
    else:
        verdict = (
            "Budget-specific assignment-bottleneck training fails closed against the matched budget-conditioned "
            "non-mechanism control."
        )

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_budget_conditioned_assignment_bottleneck",
        "feature_dims": {
            "projection_width": int(args.projection_width),
            "base_design": int(next(iter(train_base.values())).shape[1]),
            "bottleneck_design": int(next(iter(train_bottleneck.values())).shape[1]),
            "control_design": int(next(iter(train_control.values())).shape[1]),
        },
        "selection": {
            "stage": stage_selection,
            "budget_conditioned_assignment_bottleneck": bottleneck_selection,
            "budget_conditioned_nonmechanism_control": control_selection,
        },
        "hard_rows": hard_rows,
        "prediction_parity_audit": parity_audit,
        "exact_budget_cardinality_audit": exact_audit,
        "baseline_fi_100": load_baseline(Path(args.baseline)),
        "diagnosis": {
            "budget_conditioned_assignment_bottleneck_closes": closes,
            "budget_conditioned_assignment_bottleneck_beats_control": beats_control,
            "at_least_one_hard_budget_positive": at_least_one_positive,
            "bottleneck_minus_control_mean_capture": clean_float(delta),
            "bottleneck_hard_mean_capture_ratio": bottleneck_summary["mean_capture_ratio"],
            "bottleneck_hard_min_capture_ratio": bottleneck_summary["min_capture_ratio"],
            "control_hard_mean_capture_ratio": control_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": target_summary["mean_capture_ratio"],
            "prediction_parity_checked": bool(parity_audit["prediction_parity_checked"]),
            "prediction_parity_noninferior_to_control": bool(parity_audit["noninferior_to_control"]),
            "material_prediction_advantage": bool(parity_audit["material_prediction_advantage"]),
            "exact_budget_cardinality_passed": bool(exact_audit["all_rows_exact"]),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "both arms use train-standardized current/past latent-action projections and budget-fixed option designs; eval option_error is not a feature",
            "labels": "train option_error constructs forced-delta mechanism labels for supervised training; calibration option_error is used only for budget-specific model selection",
            "final_eval": "held-out hard eval episodes are used only after all budget-specific model and lambda selection",
            "matched_control": "the non-mechanism control shares projected inputs, budget exposure, target labels, ridge family, lambdas, calibration rule, and per-budget training, but omits learned assignment-state summaries",
            "oracle_scope": "the mechanism target ceiling is reported only as a reference and is not an inference-time feature",
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
        **{f"budget_{int(budget)}_score": bottleneck_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
        **{f"control_budget_{int(budget)}_score": control_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"status": "ok", "diagnosis": report["diagnosis"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
