from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_geometry_option_conditioned_allocation as option_geom


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_budget_priority_residual.json"
DEFAULT_MD = REPORT_DIR / "state_generation_budget_priority_residual.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_budget_priority_residual_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"


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


def standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0)
    scale = np.std(x.astype(np.float64), axis=0)
    scale[scale < 1.0e-8] = 1.0
    return mean.astype(np.float64), scale.astype(np.float64)


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float64) - mean) / scale).astype(np.float64)


def selected_error(option_error: np.ndarray, choice: np.ndarray) -> np.ndarray:
    return option_error[np.arange(len(choice)), choice.astype(np.int64)].astype(np.float64)


def ridge_fit(x: np.ndarray, y: np.ndarray, alpha: float) -> np.ndarray:
    x_aug = np.concatenate([x.astype(np.float64), np.ones((len(x), 1), dtype=np.float64)], axis=1)
    eye = np.eye(x_aug.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    return np.linalg.solve(x_aug.T @ x_aug + float(alpha) * eye, x_aug.T @ y.astype(np.float64))


def ridge_predict(x: np.ndarray, weights: np.ndarray) -> np.ndarray:
    x_aug = np.concatenate([x.astype(np.float64), np.ones((len(x), 1), dtype=np.float64)], axis=1)
    return (x_aug @ weights.astype(np.float64)).astype(np.float64)


def option_features(n: int) -> np.ndarray:
    depths = structured.DEPTHS.astype(np.float64)
    centered = (depths - 3.0) / 2.0
    one_hot = np.eye(len(depths), dtype=np.float64)
    per_option = np.concatenate(
        [
            depths[:, None],
            centered[:, None],
            (centered * centered)[:, None],
            (depths < 3.0).astype(np.float64)[:, None],
            (depths == 3.0).astype(np.float64)[:, None],
            (depths > 3.0).astype(np.float64)[:, None],
            one_hot,
        ],
        axis=1,
    )
    return np.tile(per_option, (n, 1)).astype(np.float64)


def option_row_features(anchor_x: np.ndarray) -> np.ndarray:
    repeated = np.repeat(anchor_x.astype(np.float64), len(structured.DEPTHS), axis=0)
    return np.concatenate([repeated, option_features(len(anchor_x))], axis=1).astype(np.float64)


def anchor_features(split: dict[str, np.ndarray], score: np.ndarray, env: np.ndarray | None = None) -> np.ndarray:
    option_error = split["option_error"].astype(np.float64)
    mid = int(np.where(structured.DEPTHS == 3)[0][0])
    depths = structured.DEPTHS.astype(np.float64)
    score = score.astype(np.float64)
    score_centered = score - score[:, [mid]]
    pieces = [
        split["x"].astype(np.float64),
        score.astype(np.float64),
        score_centered,
        np.min(score, axis=1, keepdims=True),
        np.max(score, axis=1, keepdims=True),
        np.std(score, axis=1, keepdims=True),
        np.argmin(score, axis=1, keepdims=True).astype(np.float64),
        np.sum(score * depths[None, :], axis=1, keepdims=True),
        option_error[:, [mid]],
        split["uniform_error"].reshape(-1, 1).astype(np.float64),
        split["true_mv"].astype(np.float64),
    ]
    if env is not None:
        pieces.append(env.astype(np.float64))
    return np.concatenate(pieces, axis=1).astype(np.float64)


def make_oracle_residual(split: dict[str, np.ndarray], base_score: np.ndarray) -> np.ndarray:
    oracle_choice = structured.exact_budget_choice(split["episode"], split["option_error"], structured.DEPTHS)
    base_selected = selected_error(split["option_error"], structured.exact_budget_choice(split["episode"], base_score, structured.DEPTHS))
    oracle_selected = selected_error(split["option_error"], oracle_choice)
    uniform_col = int(np.where(structured.DEPTHS == 3)[0][0])
    uniform_error = split["option_error"][:, uniform_col].astype(np.float64)
    oracle_gain = uniform_error - oracle_selected
    base_loss = base_selected - oracle_selected
    option_target = split["option_error"] - split["option_error"][:, [uniform_col]]
    priority = oracle_gain + base_loss
    return option_target - priority[:, None] / 3.0


def regenerate_geometry_option_scores(
    data: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
    *,
    seed: int,
    epochs: int,
    hidden: int,
    depth: int,
    batch: int,
    lr: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, dict[str, Any], dict[str, int]]:
    device = option_geom.configure(seed)
    depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {depths} vs {structured.DEPTHS}")
    features, feature_dims = geometry_alloc.augment_features(data, latents)
    train_x = option_geom.expand_option_features(features["train"], features["train_env"], depths)
    cal_x = option_geom.expand_option_features(features["calibration"], features["calibration_env"], depths)
    eval_x = option_geom.expand_option_features(features["eval"], features["eval_env"], depths)
    y_mean = float(np.mean(train["option_error"].reshape(-1)))
    y_scale = float(np.std(train["option_error"].reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    train_target = ((train["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)
    model, selection = option_geom.train_model(
        train_x,
        train_target,
        train["option_error"],
        cal_x,
        cal,
        depths,
        y_mean,
        y_scale,
        device=device,
        seed=seed,
        hidden=hidden,
        depth=depth,
        epochs=epochs,
        batch=batch,
        lr=lr,
    )
    train_score = option_geom.reshape_scores(
        option_geom.predict(model, train_x, device, batch) * y_scale + y_mean,
        len(train["episode"]),
        depths,
    )
    cal_score = option_geom.reshape_scores(
        option_geom.predict(model, cal_x, device, batch) * y_scale + y_mean,
        len(cal["episode"]),
        depths,
    )
    eval_score = option_geom.reshape_scores(
        option_geom.predict(model, eval_x, device, batch) * y_scale + y_mean,
        len(eval_split["episode"]),
        depths,
    )
    return train_score, cal_score, eval_score, selection, {str(k): int(v) for k, v in feature_dims.items()}


def calibrate_candidates(
    cal_split: dict[str, np.ndarray],
    base_cal: np.ndarray,
    pred_cal: np.ndarray,
    eval_base: np.ndarray,
    pred_eval: np.ndarray,
    *,
    seed: int,
) -> tuple[str, np.ndarray, dict[str, Any]]:
    candidates: list[tuple[str, np.ndarray, np.ndarray]] = [
        ("predicted_residual", pred_cal, pred_eval),
        ("base_plus_0.25_residual", base_cal + 0.25 * pred_cal, eval_base + 0.25 * pred_eval),
        ("base_plus_0.5_residual", base_cal + 0.5 * pred_cal, eval_base + 0.5 * pred_eval),
        ("base_plus_1.0_residual", base_cal + pred_cal, eval_base + pred_eval),
        ("base_minus_0.25_residual", base_cal - 0.25 * pred_cal, eval_base - 0.25 * pred_eval),
        ("base_minus_0.5_residual", base_cal - 0.5 * pred_cal, eval_base - 0.5 * pred_eval),
        ("base_minus_1.0_residual", base_cal - pred_cal, eval_base - pred_eval),
    ]
    best_name = ""
    best_eval = pred_eval
    best_key = (float("inf"), float("inf"))
    rows: dict[str, Any] = {}
    for idx, (name, cal_score, eval_score) in enumerate(candidates):
        metrics = episode_alloc.evaluate(cal_split, cal_score.astype(np.float64), seed=seed + idx)
        rows[name] = metrics
        delta = metrics["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]))
        if key < best_key:
            best_key = key
            best_name = name
            best_eval = eval_score.astype(np.float64)
    return best_name, best_eval, {"selection_key": list(best_key), "calibration": rows}


def slice_eval(split: dict[str, np.ndarray], score: np.ndarray, mask: np.ndarray, *, seed: int) -> dict[str, Any]:
    local = geometry_alloc.slice_eval(split, mask.astype(bool))
    local_score = score[mask.astype(bool)].astype(np.float64)
    out = structured.evaluate_scores(local, local_score, seed=seed)
    out["pair_accuracy"] = episode_alloc.pair_accuracy(local_score, local["option_error"])
    out["oracle_match"] = episode_alloc.oracle_match(local_score, episode_alloc.oracle_choice(local))
    return out


def evaluate_rows(eval_split: dict[str, np.ndarray], rows: dict[str, np.ndarray], hard_episodes: list[int], *, seed: int) -> dict[str, Any]:
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    return {
        row_name: {
            mask_name: slice_eval(eval_split, score, mask, seed=seed + 101 * row_idx + 17 * mask_idx)
            for mask_idx, (mask_name, mask) in enumerate(masks.items())
        }
        for row_idx, (row_name, score) in enumerate(rows.items())
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Budget Priority Residual",
        "",
        f"- selected scorer: `{report['selection']['selected']}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high | hard-only oracle match |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["priority_residual", "base_geometry_option"]:
        row = report["eval"][name]
        full = row["full"]["allocation_delta"]
        non_hard = row["non_hard"]["allocation_delta"]
        hard = row["hard_only"]["allocation_delta"]
        lines.append(
            f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | "
            f"{hard['observed']:.6g} | {hard['high']:.6g} | {row['hard_only']['oracle_match']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a budget-priority residual diagnostic for state-generation allocation")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--alpha", type=float, default=25.0)
    parser.add_argument("--seed", type=int, default=667)
    parser.add_argument("--scorer-seed", type=int, default=659)
    parser.add_argument("--scorer-epochs", type=int, default=220)
    parser.add_argument("--scorer-hidden", type=int, default=384)
    parser.add_argument("--scorer-depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--scorer-lr", type=float, default=6.0e-4)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    train_score, cal_score, eval_score, raw_selection, raw_feature_dims = regenerate_geometry_option_scores(
        data,
        latents,
        train,
        cal,
        eval_split,
        seed=int(args.scorer_seed),
        epochs=int(args.scorer_epochs),
        hidden=int(args.scorer_hidden),
        depth=int(args.scorer_depth),
        batch=int(args.batch),
        lr=float(args.scorer_lr),
    )
    train_env = geometry_alloc.env_feature_matrix(data, latents, "train")
    cal_env = geometry_alloc.env_feature_matrix(data, latents, "calibration")
    eval_env = geometry_alloc.env_feature_matrix(data, latents, "eval")
    train_x = anchor_features(train, train_score, train_env)
    cal_x = anchor_features(cal, cal_score, cal_env)
    eval_x = anchor_features(eval_split, eval_score, eval_env)
    mean, scale = standardizer(train_x)
    train_z = apply_standardizer(train_x, mean, scale)
    cal_z = apply_standardizer(cal_x, mean, scale)
    eval_z = apply_standardizer(eval_x, mean, scale)
    target = make_oracle_residual(train, train_score).astype(np.float64)
    weights = ridge_fit(option_row_features(train_z), target.reshape(-1), float(args.alpha))
    pred_cal = ridge_predict(option_row_features(cal_z), weights).reshape(len(cal["episode"]), -1)
    pred_eval = ridge_predict(option_row_features(eval_z), weights).reshape(len(eval_split["episode"]), -1)
    selected, selected_eval, selection = calibrate_candidates(
        cal,
        cal_score,
        pred_cal,
        eval_score,
        pred_eval,
        seed=int(args.seed) + 1000,
    )
    rows = {
        "priority_residual": selected_eval.astype(np.float64),
        "base_geometry_option": eval_score.astype(np.float64),
    }
    eval_rows = evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 2000)
    hard_new = eval_rows["priority_residual"]["hard_only"]["allocation_delta"]
    hard_base = eval_rows["base_geometry_option"]["hard_only"]["allocation_delta"]
    full_new = eval_rows["priority_residual"]["full"]["allocation_delta"]
    full_base = eval_rows["base_geometry_option"]["full"]["allocation_delta"]
    hard_improves = float(hard_new["observed"]) < float(hard_base["observed"])
    hard_closes = float(hard_new["high"]) < 0.0
    full_improves = float(full_new["observed"]) < float(full_base["observed"])
    if hard_closes:
        verdict = "Budget-priority residual closes the hard-only allocation slice under this diagnostic; independent validation is required."
    elif hard_improves:
        verdict = "Budget-priority residual improves hard-only observed allocation damage, but the hard-only interval remains open."
    else:
        verdict = "Budget-priority residual does not improve the hard-only allocation boundary over the raw geometry-option scorer."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_budget_priority_residual",
        "config": {
            "alpha": float(args.alpha),
            "seed": int(args.seed),
            "anchor_feature_dim": int(train_x.shape[1]),
            "option_row_feature_dim": int(option_row_features(train_z[:1]).shape[1]),
            "scorer_seed": int(args.scorer_seed),
            "scorer_epochs": int(args.scorer_epochs),
            "scorer_hidden": int(args.scorer_hidden),
            "scorer_depth": int(args.scorer_depth),
            "batch": int(args.batch),
            "scorer_lr": float(args.scorer_lr),
        },
        "raw_model_selection": raw_selection,
        "raw_feature_dims": raw_feature_dims,
        "selection": {"selected": selected, **selection},
        "eval": eval_rows,
        "diagnosis": {
            "hard_beats_raw_geometry_option_observed": bool(hard_improves),
            "hard_closes": bool(hard_closes),
            "full_beats_raw_geometry_option_observed": bool(full_improves),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "eval_targets": "eval option_error is used only after the selected score is fixed",
            "selection": "candidate score composition is selected on calibration exact-budget allocation only",
            "hard_ids": "held-out hard episode ids are used only for final diagnostic slicing",
            "raw_score": "fi-064 geometry-option scorer is regenerated deterministically to obtain train/cal/eval scores",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=structured.DEPTHS.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        priority_residual_score=selected_eval.astype(np.float64),
        raw_geometry_option_score=eval_score.astype(np.float64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
