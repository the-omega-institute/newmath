from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_hard_perturbation_value_learner as base_learner
import _state_generation_set_context_mechanism_learner as set_context


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_anchor_depth_compatibility_learner.json"
DEFAULT_MD = REPORT_DIR / "state_generation_anchor_depth_compatibility_learner.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_anchor_depth_compatibility_learner_predictions.npz"
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


def build_design(
    data: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
    split_name: str,
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    stats: dict[str, np.ndarray],
) -> np.ndarray:
    feat = set_context.build_option_features(
        data,
        latents,
        split_name,
        split,
        depths,
        x_mean=stats["x_mean"],
        x_scale=stats["x_scale"],
        x_proj=stats["x_proj"],
        env_mean=stats["env_mean"],
        env_scale=stats["env_scale"],
        mech_mean=stats["mech_mean"],
        mech_scale=stats["mech_scale"],
    )
    return set_context.design_matrix(feat, depths, BUDGETS)


def fit_stats(data: dict[str, np.ndarray], latents: dict[str, np.ndarray], depths: np.ndarray, seed: int, projection_dim: int) -> dict[str, np.ndarray]:
    x_mean, x_scale = set_context.standardizer(data["train_x"].astype(np.float32))
    x_proj = set_context.random_projector(data["train_x"].shape[1], int(projection_dim), int(seed))
    train_env = set_context.geometry_alloc.env_feature_matrix(data, latents, "train")
    env_mean, env_scale = set_context.standardizer(train_env)
    train_mech = set_context.mech_value.rollout_option_features(data, "train", depths)
    mech_mean, mech_scale = set_context.standardizer(train_mech.reshape(-1, train_mech.shape[2]))
    return {
        "x_mean": x_mean,
        "x_scale": x_scale,
        "x_proj": x_proj,
        "env_mean": env_mean,
        "env_scale": env_scale,
        "mech_mean": mech_mean,
        "mech_scale": mech_scale,
    }


def flatten_option_error(split: dict[str, np.ndarray], budgets: np.ndarray) -> np.ndarray:
    y = split["option_error"].astype(np.float64)
    return np.concatenate([y.reshape(-1) for _budget in budgets.astype(np.int64)], axis=0).astype(np.float64)


def tail_weights(y: np.ndarray, tail_weight: float) -> np.ndarray:
    threshold = float(np.quantile(y.astype(np.float64), 0.90))
    return (1.0 + float(tail_weight) * (y >= threshold).astype(np.float64)).astype(np.float64)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Anchor-Depth Compatibility Learner",
        "",
        f"- selected lambda: `{report['diagnosis']['selected_lambda']}`",
        f"- selected tail weight: `{report['diagnosis']['selected_tail_weight']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["anchor_depth_compatibility", "scalar_mechanism", "set_context_mechanism", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an anchor-depth compatibility cost learner for exact-budget assignment")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(set_context.env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--scalar-pred", default=str(SCALAR_PRED))
    parser.add_argument("--set-context-pred", default=str(SET_CONTEXT_PRED))
    parser.add_argument("--base-pred", default=str(BASE_PRED))
    parser.add_argument("--target-pred", default=str(TARGET_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=3251)
    parser.add_argument("--projection-dim", type=int, default=12)
    parser.add_argument("--bootstrap-samples", type=int, default=80)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    depths = data["option_depths"].astype(np.int64)
    train = set_context.episode_alloc.load_split(data, "train")
    cal = set_context.episode_alloc.load_split(data, "calibration")
    eval_split = set_context.episode_alloc.load_split(data, "eval")
    hard_episodes = set_context.env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    stats = fit_stats(data, latents, depths, int(args.seed), int(args.projection_dim))
    train_x = build_design(data, latents, "train", train, depths, stats)
    cal_x = build_design(data, latents, "calibration", cal, depths, stats)
    eval_x = build_design(data, latents, "eval", eval_split, depths, stats)
    train_y_raw = flatten_option_error(train, BUDGETS)
    y_mean = float(np.mean(train_y_raw))
    y_scale = float(np.std(train_y_raw))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    train_y = ((train_y_raw - y_mean) / y_scale).astype(np.float64)
    cal_rows: list[dict[str, Any]] = []
    best_key = (float("inf"), float("inf"), float("inf"))
    best_beta: np.ndarray | None = None
    best_cfg: dict[str, float] = {}
    for lam in (100.0, 10000.0):
        for tw in (0.0, 4.0):
            weights = tail_weights(train_y_raw, tw)
            beta, _ = set_context.weighted_ridge(train_x, train_y, weights, lam)
            cal_scores_z = set_context.predict_scores(cal_x, beta, len(cal["episode"]), depths, BUDGETS)
            cal_scores = {int(budget): cal_scores_z[int(budget)] * y_scale + y_mean for budget in BUDGETS}
            mean_cap, min_cap, regret = set_context.observed_capture(cal, cal_scores, np.ones(len(cal["episode"]), dtype=bool))
            rho = set_context.label_rho(cal, depths, cal_scores)
            key = (-mean_cap, -min_cap, regret)
            row = {
                "lambda": clean_float(lam),
                "tail_weight": clean_float(tw),
                "cal_mean_capture_ratio": mean_cap,
                "cal_min_capture_ratio": min_cap,
                "cal_mean_label_rho": rho,
                "cal_mean_regret_to_oracle": regret,
                "selection_key": [clean_float(v) for v in key],
            }
            cal_rows.append(row)
            if key < best_key:
                best_key = key
                best_beta = beta
                best_cfg = {"lambda": clean_float(lam), "tail_weight": clean_float(tw)}
    if best_beta is None:
        raise RuntimeError("no compatibility candidate selected")

    eval_scores_z = set_context.predict_scores(eval_x, best_beta, len(eval_split["episode"]), depths, BUDGETS)
    eval_scores = {int(budget): eval_scores_z[int(budget)] * y_scale + y_mean for budget in BUDGETS}
    scalar = load_scores(Path(args.scalar_pred))
    set_ctx = load_scores(Path(args.set_context_pred))
    base = load_scores(Path(args.base_pred))
    target = load_scores(Path(args.target_pred))
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "anchor_depth_compatibility": eval_scores,
            "scalar_mechanism": scalar,
            "set_context_mechanism": set_ctx,
            "base_perturbation_value": base,
            "mechanism_target_ceiling": target,
        }.items()
    ):
        hard_rows[name] = {
            "capture": set_context.capture_summary(eval_split, scores, hard_mask, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples)),
            "label_alignment": base_learner.hard_label_alignment(eval_split, depths, BUDGETS, hard_episodes, scores),
        }

    comp_summary = hard_rows["anchor_depth_compatibility"]["capture"]["summary"]
    scalar_summary = hard_rows["scalar_mechanism"]["capture"]["summary"]
    base_summary = hard_rows["base_perturbation_value"]["capture"]["summary"]
    closes = bool(float(comp_summary["mean_capture_ratio"]) > 0.0 and float(comp_summary["min_capture_ratio"]) > 0.0)
    improves_scalar = bool(float(comp_summary["mean_capture_ratio"]) > float(scalar_summary["mean_capture_ratio"]))
    improves_base = bool(float(comp_summary["mean_capture_ratio"]) > float(base_summary["mean_capture_ratio"]))
    verdict = (
        "Anchor-depth compatibility learning closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "Anchor-depth compatibility learning improves the hard mechanism route but does not close all hard exact-budget budgets."
        if improves_scalar or improves_base
        else "Anchor-depth compatibility learning does not improve held-out hard exact-budget capture over the scalar mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_anchor_depth_compatibility_learner",
        "feature_dim": int(train_x.shape[1]),
        "target_stats": {"mean": clean_float(y_mean), "scale": clean_float(y_scale)},
        "calibration_candidates": cal_rows,
        "hard_rows": hard_rows,
        "diagnosis": {
            "anchor_depth_compatibility_closes": closes,
            "selected_lambda": best_cfg["lambda"],
            "selected_tail_weight": best_cfg["tail_weight"],
            "compatibility_hard_mean_capture_ratio": comp_summary["mean_capture_ratio"],
            "compatibility_hard_min_capture_ratio": comp_summary["min_capture_ratio"],
            "scalar_hard_mean_capture_ratio": scalar_summary["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": hard_rows["mechanism_target_ceiling"]["capture"]["summary"]["mean_capture_ratio"],
            "compatibility_improves_scalar": improves_scalar,
            "compatibility_improves_base": improves_base,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "train_label_scope": "train option_error is used as the anchor-depth compatibility cost target",
            "selection_scope": "calibration option_error is used only for exact-budget capture and candidate selection",
            "eval_scope": "eval option_error is used only for held-out hard capture and label-alignment measurement",
            "feature_scope": "model inputs are latent, environment, rollout-internal, episode-local set context, depth, and budget features; eval option_error is not a feature",
            "target_ceiling_scope": "mechanism target ceiling is reference-only and excluded from selection",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy beyond this export", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(Path(args.out), **{f"budget_{int(budget)}_score": eval_scores[int(budget)].astype(np.float32) for budget in BUDGETS})
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps({"status": "ok", "diagnosis": report["diagnosis"]}, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
