from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured
import _state_generation_budget_priority_residual as priority_residual
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_assignment_value as episode_value
import _state_generation_geometry_conditioned_allocation as geometry_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_residual_benefit_selector.json"
DEFAULT_MD = REPORT_DIR / "state_generation_residual_benefit_selector.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_residual_benefit_selector_predictions.npz"
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


def selected_error(option_error: np.ndarray, choice: np.ndarray) -> np.ndarray:
    return option_error[np.arange(len(choice)), choice.astype(np.int64)].astype(np.float64)


def standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0)
    scale = np.std(x.astype(np.float64), axis=0)
    scale[scale < 1.0e-8] = 1.0
    return mean.astype(np.float64), scale.astype(np.float64)


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float64) - mean) / scale).astype(np.float64)


def ridge_fit(x: np.ndarray, y: np.ndarray, alpha: float) -> np.ndarray:
    x_aug = np.concatenate([x.astype(np.float64), np.ones((len(x), 1), dtype=np.float64)], axis=1)
    eye = np.eye(x_aug.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    return np.linalg.solve(x_aug.T @ x_aug + float(alpha) * eye, x_aug.T @ y.astype(np.float64))


def ridge_predict(x: np.ndarray, weights: np.ndarray) -> np.ndarray:
    x_aug = np.concatenate([x.astype(np.float64), np.ones((len(x), 1), dtype=np.float64)], axis=1)
    return (x_aug @ weights.astype(np.float64)).astype(np.float64)


def episode_summary(split: dict[str, np.ndarray], parts: np.ndarray) -> np.ndarray:
    out = np.zeros_like(parts, dtype=np.float64)
    episode = split["episode"].astype(np.int64)
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep))
        block = parts[idx].astype(np.float64)
        out[idx] = np.mean(block, axis=0) + 0.5 * np.std(block, axis=0)
    return out.astype(np.float64)


def benefit_features(
    split: dict[str, np.ndarray],
    raw_score: np.ndarray,
    priority_score: np.ndarray,
    env: np.ndarray,
) -> np.ndarray:
    raw = raw_score.astype(np.float64)
    priority = priority_score.astype(np.float64)
    mid = int(np.where(structured.DEPTHS == 3)[0][0])
    score_parts = np.concatenate(
        [
            raw,
            priority,
            priority - raw,
            raw - raw[:, [mid]],
            priority - priority[:, [mid]],
            np.std(raw, axis=1, keepdims=True),
            np.std(priority, axis=1, keepdims=True),
            np.argmin(raw, axis=1, keepdims=True).astype(np.float64),
            np.argmin(priority, axis=1, keepdims=True).astype(np.float64),
            env.astype(np.float64),
        ],
        axis=1,
    )
    return np.concatenate([split["x"].astype(np.float64), score_parts, episode_summary(split, score_parts)], axis=1)


def assignment_benefit(split: dict[str, np.ndarray], raw_score: np.ndarray, priority_score: np.ndarray) -> np.ndarray:
    raw_choice = structured.exact_budget_choice(split["episode"], raw_score.astype(np.float64), structured.DEPTHS)
    priority_choice = structured.exact_budget_choice(split["episode"], priority_score.astype(np.float64), structured.DEPTHS)
    raw_error = selected_error(split["option_error"].astype(np.float64), raw_choice)
    priority_error = selected_error(split["option_error"].astype(np.float64), priority_choice)
    return (raw_error - priority_error).astype(np.float64)


def mix_scores(raw_score: np.ndarray, priority_score: np.ndarray, use_priority: np.ndarray) -> np.ndarray:
    out = raw_score.astype(np.float64).copy()
    mask = use_priority.astype(bool)
    out[mask] = priority_score.astype(np.float64)[mask]
    return out


def candidate_thresholds(train_pred: np.ndarray) -> list[float]:
    qs = [0.05, 0.10, 0.20, 0.35, 0.50, 0.65, 0.80, 0.90, 0.95]
    values = [float(np.quantile(train_pred.astype(np.float64), q)) for q in qs]
    values.append(0.0)
    return sorted(set(round(v, 12) for v in values))


def select_candidate(
    cal_split: dict[str, np.ndarray],
    raw_cal: np.ndarray,
    priority_cal: np.ndarray,
    pred_cal: np.ndarray,
    raw_eval: np.ndarray,
    priority_eval: np.ndarray,
    pred_eval: np.ndarray,
    thresholds: list[float],
    *,
    seed: int,
) -> tuple[str, np.ndarray, dict[str, Any]]:
    candidates: list[tuple[str, np.ndarray, np.ndarray]] = [
        ("raw_geometry_option", raw_cal, raw_eval),
        ("priority_residual", priority_cal, priority_eval),
    ]
    for threshold in thresholds:
        name = f"benefit_switch_ge_{threshold:.6g}"
        candidates.append(
            (
                name,
                mix_scores(raw_cal, priority_cal, pred_cal >= threshold),
                mix_scores(raw_eval, priority_eval, pred_eval >= threshold),
            )
        )
    best_name = ""
    best_eval: np.ndarray | None = None
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
    if best_eval is None:
        raise RuntimeError("no candidate selected")
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
    out: dict[str, Any] = {}
    for row_idx, (name, score) in enumerate(rows.items()):
        out[name] = {
            slice_name: slice_eval(eval_split, score, mask, seed=seed + 101 * row_idx + 17 * slice_idx)
            for slice_idx, (slice_name, mask) in enumerate(masks.items())
        }
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Residual Benefit Selector",
        "",
        f"- selected scorer: `{report['selection']['selected']}`",
        f"- train benefit correlation: `{report['benefit_model']['train_corr']:.6g}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high |",
        "|---|---:|---:|---:|---:|",
    ]
    for name in ["benefit_selector", "priority_residual", "raw_geometry_option"]:
        row = report["eval"][name]
        full = row["full"]["allocation_delta"]
        non_hard = row["non_hard"]["allocation_delta"]
        hard = row["hard_only"]["allocation_delta"]
        lines.append(f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | {hard['observed']:.6g} | {hard['high']:.6g} |")
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def corr(x: np.ndarray, y: np.ndarray) -> float:
    x = x.astype(np.float64)
    y = y.astype(np.float64)
    if len(x) < 2 or float(np.std(x)) < 1.0e-12 or float(np.std(y)) < 1.0e-12:
        return 0.0
    return float(np.corrcoef(x, y)[0, 1])


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a train/cal residual-benefit selector for raw vs priority allocation scores")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=727)
    parser.add_argument("--alpha", type=float, default=15.0)
    parser.add_argument("--scorer-seed", type=int, default=659)
    parser.add_argument("--scorer-epochs", type=int, default=60)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    train_raw, cal_raw, eval_raw, raw_selection, raw_feature_dims = priority_residual.regenerate_geometry_option_scores(
        data,
        latents,
        train,
        cal,
        eval_split,
        seed=int(args.scorer_seed),
        epochs=int(args.scorer_epochs),
        hidden=384,
        depth=2,
        batch=512,
        lr=6.0e-4,
    )
    train_env = geometry_alloc.env_feature_matrix(data, latents, "train")
    cal_env = geometry_alloc.env_feature_matrix(data, latents, "calibration")
    eval_env = geometry_alloc.env_feature_matrix(data, latents, "eval")
    train_priority, cal_priority, eval_priority, priority_selected = episode_value.priority_scores(
        train,
        cal,
        eval_split,
        train_raw,
        cal_raw,
        eval_raw,
        train_env,
        cal_env,
        eval_env,
        alpha=25.0,
        seed=int(args.seed) + 1000,
    )
    train_x = benefit_features(train, train_raw, train_priority, train_env)
    cal_x = benefit_features(cal, cal_raw, cal_priority, cal_env)
    eval_x = benefit_features(eval_split, eval_raw, eval_priority, eval_env)
    mean, scale = standardizer(train_x)
    train_z = apply_standardizer(train_x, mean, scale)
    cal_z = apply_standardizer(cal_x, mean, scale)
    eval_z = apply_standardizer(eval_x, mean, scale)
    train_benefit = assignment_benefit(train, train_raw, train_priority)
    weights = ridge_fit(train_z, train_benefit, float(args.alpha))
    train_pred = ridge_predict(train_z, weights)
    cal_pred = ridge_predict(cal_z, weights)
    eval_pred = ridge_predict(eval_z, weights)
    thresholds = candidate_thresholds(train_pred)
    selected, selected_eval, selection = select_candidate(
        cal,
        cal_raw,
        cal_priority,
        cal_pred,
        eval_raw,
        eval_priority,
        eval_pred,
        thresholds,
        seed=int(args.seed) + 2000,
    )
    rows = {
        "benefit_selector": selected_eval.astype(np.float64),
        "priority_residual": eval_priority.astype(np.float64),
        "raw_geometry_option": eval_raw.astype(np.float64),
    }
    eval_rows = evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 3000)
    hard_selected = eval_rows["benefit_selector"]["hard_only"]["allocation_delta"]
    hard_priority = eval_rows["priority_residual"]["hard_only"]["allocation_delta"]
    hard_raw = eval_rows["raw_geometry_option"]["hard_only"]["allocation_delta"]
    beats_priority = float(hard_selected["observed"]) < float(hard_priority["observed"])
    beats_raw = float(hard_selected["observed"]) < float(hard_raw["observed"])
    hard_closes = float(hard_selected["high"]) < 0.0
    if hard_closes:
        verdict = "Residual-benefit selector closes the hard-only allocation slice under this diagnostic; independent validation is required."
    elif beats_priority:
        verdict = "Residual-benefit selector improves over priority residual on the hard-only slice, but the hard interval remains open."
    elif beats_raw:
        verdict = "Residual-benefit selector improves over raw geometry-option scores but does not beat priority residual."
    else:
        verdict = "Residual-benefit selector does not improve the hard-only allocation boundary over raw geometry-option scores."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_residual_benefit_selector",
        "config": {
            "seed": int(args.seed),
            "alpha": float(args.alpha),
            "scorer_seed": int(args.scorer_seed),
            "scorer_epochs": int(args.scorer_epochs),
            "feature_dim": int(train_x.shape[1]),
            "threshold_count": int(len(thresholds)),
        },
        "raw_model_selection": raw_selection,
        "raw_feature_dims": raw_feature_dims,
        "priority_selection": priority_selected,
        "benefit_model": {
            "train_corr": corr(train_pred, train_benefit),
            "train_benefit_mean": clean_float(float(np.mean(train_benefit))),
            "train_benefit_std": clean_float(float(np.std(train_benefit))),
            "eval_pred_mean": clean_float(float(np.mean(eval_pred))),
            "eval_pred_std": clean_float(float(np.std(eval_pred))),
        },
        "selection": {"selected": selected, **selection},
        "eval": eval_rows,
        "diagnosis": {
            "hard_beats_priority_residual_observed": bool(beats_priority),
            "hard_beats_raw_geometry_option_observed": bool(beats_raw),
            "hard_closes": bool(hard_closes),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "raw_score": "geometry-option scorer is regenerated deterministically",
            "priority_score": "budget-priority residual is trained on train targets and selected on calibration exact-budget allocation",
            "benefit_label": "raw-vs-priority benefit labels are computed on train exact-budget assignments only",
            "threshold_selection": "raw-vs-priority switch threshold is selected on calibration exact-budget allocation",
            "eval_targets": "eval option_error is used only after all scores are fixed",
            "hard_ids": "held-out hard episode ids are used only for final diagnostic slicing",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure unless hard CI high < 0", "deployable policy", "independent export validation"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=structured.DEPTHS.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        benefit_selector_score=selected_eval.astype(np.float64),
        priority_residual_score=eval_priority.astype(np.float64),
        raw_geometry_option_score=eval_raw.astype(np.float64),
        predicted_benefit=eval_pred.astype(np.float64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
