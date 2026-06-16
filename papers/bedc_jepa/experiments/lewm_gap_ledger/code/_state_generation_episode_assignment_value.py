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
import _state_generation_episode_regret as episode_regret
import _state_generation_geometry_conditioned_allocation as geometry_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_assignment_value.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_assignment_value.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_episode_assignment_value_predictions.npz"
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


def episode_context(split: dict[str, np.ndarray], raw_score: np.ndarray, priority_score: np.ndarray, env: np.ndarray) -> np.ndarray:
    parts = np.concatenate(
        [
            raw_score.astype(np.float64),
            priority_score.astype(np.float64),
            np.std(raw_score.astype(np.float64), axis=1, keepdims=True),
            np.std(priority_score.astype(np.float64), axis=1, keepdims=True),
            env.astype(np.float64),
        ],
        axis=1,
    )
    context = np.zeros_like(parts, dtype=np.float64)
    episode = split["episode"].astype(np.int64)
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep))
        block = parts[idx]
        summary = np.concatenate(
            [
                np.mean(block, axis=0),
                np.std(block, axis=0),
            ]
        )
        # Compress the episode summary back to the same width by folding mean
        # and spread; this keeps the model small while still exposing
        # episode-level budget context.
        context[idx] = summary[: parts.shape[1]] + 0.5 * summary[parts.shape[1] :]
    return context.astype(np.float64)


def build_features(
    split: dict[str, np.ndarray],
    raw_score: np.ndarray,
    priority_score: np.ndarray,
    env: np.ndarray,
) -> np.ndarray:
    ctx = episode_context(split, raw_score, priority_score, env)
    per_anchor = np.concatenate(
        [
            split["x"].astype(np.float64),
            env.astype(np.float64),
            raw_score.astype(np.float64),
            priority_score.astype(np.float64),
            raw_score.astype(np.float64) - raw_score[:, [2]],
            priority_score.astype(np.float64) - priority_score[:, [2]],
            ctx,
        ],
        axis=1,
    )
    return per_anchor.astype(np.float64)


def priority_scores(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
    train_score: np.ndarray,
    cal_score: np.ndarray,
    eval_score: np.ndarray,
    train_env: np.ndarray,
    cal_env: np.ndarray,
    eval_env: np.ndarray,
    *,
    alpha: float,
    seed: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, str]:
    train_x = priority_residual.anchor_features(train, train_score, train_env)
    cal_x = priority_residual.anchor_features(cal, cal_score, cal_env)
    eval_x = priority_residual.anchor_features(eval_split, eval_score, eval_env)
    mean, scale = priority_residual.standardizer(train_x)
    train_z = priority_residual.apply_standardizer(train_x, mean, scale)
    cal_z = priority_residual.apply_standardizer(cal_x, mean, scale)
    eval_z = priority_residual.apply_standardizer(eval_x, mean, scale)
    target = priority_residual.make_oracle_residual(train, train_score).astype(np.float64)
    weights = priority_residual.ridge_fit(priority_residual.option_row_features(train_z), target.reshape(-1), alpha)
    pred_cal = priority_residual.ridge_predict(priority_residual.option_row_features(cal_z), weights).reshape(len(cal["episode"]), -1)
    pred_eval = priority_residual.ridge_predict(priority_residual.option_row_features(eval_z), weights).reshape(len(eval_split["episode"]), -1)
    selected, selected_eval, selection = priority_residual.calibrate_candidates(
        cal,
        cal_score,
        pred_cal,
        eval_score,
        pred_eval,
        seed=seed,
    )
    # Reconstruct the selected calibration score for downstream training.
    selected_cal = selection["calibration"][selected]
    _ = selected_cal  # kept for report symmetry; score reconstruction follows the selected name.
    if selected == "predicted_residual":
        cal_priority = pred_cal
    elif selected.startswith("base_plus_"):
        scale_value = float(selected.split("_")[2])
        cal_priority = cal_score + scale_value * pred_cal
    elif selected.startswith("base_minus_"):
        scale_value = float(selected.split("_")[2])
        cal_priority = cal_score - scale_value * pred_cal
    else:
        raise ValueError(f"unsupported priority candidate: {selected}")
    train_pred = priority_residual.ridge_predict(
        priority_residual.option_row_features(train_z), weights
    ).reshape(len(train["episode"]), -1)
    train_priority = train_score + train_pred
    if selected.startswith("base_plus_"):
        scale_value = float(selected.split("_")[2])
        train_priority = train_score + scale_value * (train_priority - train_score)
    elif selected.startswith("base_minus_"):
        scale_value = float(selected.split("_")[2])
        train_priority = train_score - scale_value * (train_priority - train_score)
    elif selected == "predicted_residual":
        train_priority = train_pred
    return train_priority.astype(np.float64), cal_priority.astype(np.float64), selected_eval.astype(np.float64), selected


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
        "# State-Generation Episode Assignment Value",
        "",
        f"- selected priority seed row: `{report['priority_selection']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high | hard-only oracle match |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["episode_assignment_value", "priority_residual", "base_geometry_option"]:
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
    parser = argparse.ArgumentParser(description="Train an episode-aware assignment-value scorer")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=681)
    parser.add_argument("--epochs", type=int, default=48)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    parser.add_argument("--competitors", type=int, default=12)
    parser.add_argument("--scorer-epochs", type=int, default=80)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    train_score, cal_score, eval_score, raw_selection, raw_feature_dims = priority_residual.regenerate_geometry_option_scores(
        data,
        latents,
        train,
        cal,
        eval_split,
        seed=659,
        epochs=int(args.scorer_epochs),
        hidden=384,
        depth=2,
        batch=512,
        lr=6.0e-4,
    )
    train_env = geometry_alloc.env_feature_matrix(data, latents, "train")
    cal_env = geometry_alloc.env_feature_matrix(data, latents, "calibration")
    eval_env = geometry_alloc.env_feature_matrix(data, latents, "eval")
    train_priority, cal_priority, eval_priority, priority_selection = priority_scores(
        train,
        cal,
        eval_split,
        train_score,
        cal_score,
        eval_score,
        train_env,
        cal_env,
        eval_env,
        alpha=25.0,
        seed=int(args.seed) + 1000,
    )
    train_feat = build_features(train, train_score, train_priority, train_env)
    cal_feat = build_features(cal, cal_score, cal_priority, cal_env)
    eval_feat = build_features(eval_split, eval_score, eval_priority, eval_env)
    mean, scale = episode_alloc.standardizer(train_feat)
    train_x = episode_alloc.apply_standardizer(train_feat, mean, scale)
    cal_x = episode_alloc.apply_standardizer(cal_feat, mean, scale)
    eval_x = episode_alloc.apply_standardizer(eval_feat, mean, scale)
    train_oracle = episode_alloc.oracle_choice(train)
    eval_oracle = episode_alloc.oracle_choice(eval_split)
    device = episode_regret.configure(int(args.seed))
    model, selection = episode_regret.train_model(
        train_x,
        train,
        train_oracle,
        cal_x,
        cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        lr=float(args.lr),
        competitor_count=int(args.competitors),
    )
    eval_assignment = episode_alloc.predict(model, eval_x, device, 256)
    rows = {
        "episode_assignment_value": eval_assignment.astype(np.float64),
        "priority_residual": eval_priority.astype(np.float64),
        "base_geometry_option": eval_score.astype(np.float64),
    }
    eval_rows = evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 3000)
    hard_new = eval_rows["episode_assignment_value"]["hard_only"]["allocation_delta"]
    hard_priority = eval_rows["priority_residual"]["hard_only"]["allocation_delta"]
    hard_base = eval_rows["base_geometry_option"]["hard_only"]["allocation_delta"]
    hard_closes = float(hard_new["high"]) < 0.0
    beats_priority = float(hard_new["observed"]) < float(hard_priority["observed"])
    beats_base = float(hard_new["observed"]) < float(hard_base["observed"])
    if hard_closes:
        verdict = "Episode-aware assignment-value scorer closes the hard-only allocation slice under this diagnostic; independent validation is required."
    elif beats_priority:
        verdict = "Episode-aware assignment-value scorer improves over the priority-residual hard-only movement, but the hard interval remains open."
    elif beats_base:
        verdict = "Episode-aware assignment-value scorer improves over raw geometry-option scores but does not beat the priority-residual movement."
    else:
        verdict = "Episode-aware assignment-value scorer does not improve the hard-only allocation boundary over the raw geometry-option scorer."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_assignment_value",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "lr": float(args.lr),
            "competitors": int(args.competitors),
            "scorer_epochs": int(args.scorer_epochs),
            "feature_dim": int(train_x.shape[1]),
        },
        "raw_model_selection": raw_selection,
        "raw_feature_dims": raw_feature_dims,
        "priority_selection": priority_selection,
        "selection": selection,
        "eval": eval_rows,
        "diagnosis": {
            "hard_beats_priority_residual_observed": bool(beats_priority),
            "hard_beats_raw_geometry_option_observed": bool(beats_base),
            "hard_closes": bool(hard_closes),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "raw_score": "fi-064 geometry-option scorer is regenerated deterministically to obtain train/cal/eval scores",
            "priority_score": "budget-priority residual is trained on train targets and selected on calibration exact-budget allocation",
            "assignment_value": "episode-aware scorer is trained on train exact-budget oracle/competitors and selected on calibration exact-budget allocation",
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
        episode_assignment_value_score=eval_assignment.astype(np.float64),
        priority_residual_score=eval_priority.astype(np.float64),
        raw_geometry_option_score=eval_score.astype(np.float64),
        oracle_choice=eval_oracle.astype(np.int64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
