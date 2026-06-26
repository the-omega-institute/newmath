from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured
import _state_generation_episode_allocation as episode_alloc
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_geometry_option_conditioned_allocation as option_geom


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_calibration_transform.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_calibration_transform.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_episode_calibration_transform_predictions.npz"
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


def fit_affine(x: np.ndarray, y: np.ndarray, alpha: float) -> np.ndarray:
    x_aug = np.stack([x.astype(np.float64), np.ones(len(x), dtype=np.float64)], axis=1)
    eye = np.eye(2, dtype=np.float64)
    eye[-1, -1] = 0.0
    return np.linalg.solve(x_aug.T @ x_aug + float(alpha) * eye, x_aug.T @ y.astype(np.float64))


def apply_affine(x: np.ndarray, weights: np.ndarray) -> np.ndarray:
    return (float(weights[0]) * x.astype(np.float64) + float(weights[1])).astype(np.float64)


def global_affine(cal_score: np.ndarray, cal_error: np.ndarray, eval_score: np.ndarray, alpha: float) -> tuple[np.ndarray, np.ndarray]:
    weights = fit_affine(cal_score.reshape(-1), cal_error.reshape(-1), alpha)
    return apply_affine(cal_score, weights), apply_affine(eval_score, weights)


def per_depth_affine(cal_score: np.ndarray, cal_error: np.ndarray, eval_score: np.ndarray, alpha: float) -> tuple[np.ndarray, np.ndarray]:
    cal_out = np.zeros_like(cal_score, dtype=np.float64)
    eval_out = np.zeros_like(eval_score, dtype=np.float64)
    for col in range(cal_score.shape[1]):
        weights = fit_affine(cal_score[:, col], cal_error[:, col], alpha)
        cal_out[:, col] = apply_affine(cal_score[:, col], weights)
        eval_out[:, col] = apply_affine(eval_score[:, col], weights)
    return cal_out, eval_out


def anchor_centered(score: np.ndarray, gamma: float) -> np.ndarray:
    mean = np.mean(score.astype(np.float64), axis=1, keepdims=True)
    return (mean + float(gamma) * (score.astype(np.float64) - mean)).astype(np.float64)


def depth_bias(score: np.ndarray, lam: float) -> np.ndarray:
    centered_depth = structured.DEPTHS.astype(np.float64) - 3.0
    return (score.astype(np.float64) + float(lam) * centered_depth[None, :]).astype(np.float64)


def train_regime_masks(train_env: np.ndarray, env: np.ndarray) -> dict[str, np.ndarray]:
    threshold = float(np.quantile(train_env[:, 3].astype(np.float64), 0.30))
    low_y = env[:, 3].astype(np.float64) <= threshold
    diff_room = env[:, 9].astype(np.float64) >= 0.5
    return {
        "all": np.ones(len(env), dtype=bool),
        "low_y": low_y.astype(bool),
        "different_room": diff_room.astype(bool),
        "low_y_different_room": (low_y & diff_room).astype(bool),
    }


def regime_scaled(score: np.ndarray, masks: dict[str, np.ndarray], regime_name: str, gamma: float) -> np.ndarray:
    out = score.astype(np.float64).copy()
    mask = masks[regime_name].astype(bool)
    if np.any(mask):
        mean = np.mean(out[mask], axis=1, keepdims=True)
        out[mask] = mean + float(gamma) * (out[mask] - mean)
    return out


def make_candidates(
    cal_score: np.ndarray,
    cal_error: np.ndarray,
    eval_score: np.ndarray,
    train_env_raw: np.ndarray,
    cal_env_raw: np.ndarray,
    eval_env_raw: np.ndarray,
) -> list[tuple[str, np.ndarray, np.ndarray]]:
    candidates: list[tuple[str, np.ndarray, np.ndarray]] = [("base", cal_score, eval_score)]
    for alpha in (0.001, 0.01, 0.1, 1.0, 10.0):
        candidates.append((f"global_affine_alpha_{alpha:g}", *global_affine(cal_score, cal_error, eval_score, alpha)))
        candidates.append((f"per_depth_affine_alpha_{alpha:g}", *per_depth_affine(cal_score, cal_error, eval_score, alpha)))
    for gamma in (0.25, 0.5, 0.75, 1.25, 1.5, 2.0):
        candidates.append((f"anchor_centered_gamma_{gamma:g}", anchor_centered(cal_score, gamma), anchor_centered(eval_score, gamma)))
    centered_depth = structured.DEPTHS.astype(np.float64) - 3.0
    spread = float(np.std(cal_score.astype(np.float64) @ centered_depth))
    radius = max(0.02, spread)
    for lam in np.linspace(-radius, radius, 9, dtype=np.float64):
        candidates.append((f"depth_bias_lambda_{lam:.6g}", depth_bias(cal_score, float(lam)), depth_bias(eval_score, float(lam))))
    cal_masks = train_regime_masks(train_env_raw, cal_env_raw)
    eval_masks = train_regime_masks(train_env_raw, eval_env_raw)
    for regime in ("low_y", "different_room", "low_y_different_room"):
        for gamma in (0.5, 0.75, 1.25, 1.5, 2.0):
            candidates.append(
                (
                    f"regime_{regime}_gamma_{gamma:g}",
                    regime_scaled(cal_score, cal_masks, regime, gamma),
                    regime_scaled(eval_score, eval_masks, regime, gamma),
                )
            )
    return candidates


def evaluate_slice(split: dict[str, np.ndarray], score: np.ndarray, mask: np.ndarray, *, seed: int) -> dict[str, Any]:
    local = geometry_alloc.slice_eval(split, mask.astype(bool))
    local_score = score[mask.astype(bool)].astype(np.float64)
    metrics = structured.evaluate_scores(local, local_score, seed=seed)
    metrics["score_error_spearman"] = clean_float(structured.cvm.spearman(local_score.reshape(-1), local["option_error"].reshape(-1)))
    metrics["pair_accuracy"] = episode_alloc.pair_accuracy(local_score, local["option_error"])
    return metrics


def evaluate_rows(
    eval_split: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    hard_episodes: list[int],
    *,
    seed: int,
) -> dict[str, Any]:
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    out: dict[str, Any] = {}
    for row_idx, (name, score) in enumerate(rows.items()):
        out[name] = {
            slice_name: evaluate_slice(eval_split, score, mask, seed=seed + row_idx * 101 + slice_idx * 17)
            for slice_idx, (slice_name, mask) in enumerate(masks.items())
        }
    return out


def select_transform(cal_split: dict[str, np.ndarray], candidates: list[tuple[str, np.ndarray, np.ndarray]], seed: int) -> dict[str, Any]:
    best_name = ""
    best_key = (float("inf"), float("inf"))
    best_eval_score: np.ndarray | None = None
    rows: dict[str, Any] = {}
    for idx, (name, cal_score, eval_score) in enumerate(candidates):
        metrics = structured.evaluate_scores(cal_split, cal_score.astype(np.float64), seed=seed + idx)
        metrics["score_error_spearman"] = clean_float(
            structured.cvm.spearman(cal_score.reshape(-1), cal_split["option_error"].reshape(-1))
        )
        rows[name] = metrics
        delta = metrics["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]))
        if key < best_key:
            best_name = name
            best_key = key
            best_eval_score = eval_score.astype(np.float64)
    if best_eval_score is None:
        raise RuntimeError("no calibration transform candidate selected")
    return {
        "selected": best_name,
        "selection_key": list(best_key),
        "calibration": rows,
        "eval_score": best_eval_score,
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Episode Calibration Transform",
        "",
        f"- selected transform: `{report['selection']['selected']}`",
        f"- raw score source: `{report['raw_score_source']}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high | hard-only rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["calibrated", "base_geometry_option", "geometry_conditioned", "geometry_regime_weighted"]:
        row = report["eval"][name]
        full = row["full"]["allocation_delta"]
        non_hard = row["non_hard"]["allocation_delta"]
        hard = row["hard_only"]["allocation_delta"]
        lines.append(
            f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | "
            f"{hard['observed']:.6g} | {hard['high']:.6g} | {row['hard_only']['score_error_spearman']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate calibration transforms for geometry-option allocation scores")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--seed", type=int, default=659)
    parser.add_argument("--epochs", type=int, default=220)
    parser.add_argument("--hidden", type=int, default=384)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=6.0e-4)
    args = parser.parse_args()
    start_time = time.time()
    device = option_geom.configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
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
    model, raw_selection = option_geom.train_model(
        train_x,
        train_target,
        train["option_error"],
        cal_x,
        cal,
        depths,
        y_mean,
        y_scale,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    cal_score = option_geom.reshape_scores(
        option_geom.predict(model, cal_x, device, int(args.batch)) * y_scale + y_mean,
        len(cal["episode"]),
        depths,
    )
    eval_score = option_geom.reshape_scores(
        option_geom.predict(model, eval_x, device, int(args.batch)) * y_scale + y_mean,
        len(eval_split["episode"]),
        depths,
    )
    train_env_raw = geometry_alloc.env_feature_matrix(data, latents, "train")
    cal_env_raw = geometry_alloc.env_feature_matrix(data, latents, "calibration")
    eval_env_raw = geometry_alloc.env_feature_matrix(data, latents, "eval")
    candidates = make_candidates(cal_score, cal["option_error"], eval_score, train_env_raw, cal_env_raw, eval_env_raw)
    transform_selection = select_transform(cal, candidates, seed=int(args.seed) + 7000)
    calibrated_score = transform_selection["eval_score"].astype(np.float64)
    with np.load(REPORT_DIR / "state_generation_geometry_conditioned_allocation_predictions.npz", allow_pickle=False) as geom:
        geometry_conditioned = geom["geometry_conditioned_score"].astype(np.float64)
    with np.load(REPORT_DIR / "state_generation_geometry_regime_weighted_allocation_predictions.npz", allow_pickle=False) as regime:
        geometry_regime_weighted = regime["geometry_regime_weighted_score"].astype(np.float64)
    rows = {
        "calibrated": calibrated_score,
        "base_geometry_option": eval_score,
        "geometry_conditioned": geometry_conditioned,
        "geometry_regime_weighted": geometry_regime_weighted,
    }
    eval_rows = evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 8000)
    calibrated_hard = eval_rows["calibrated"]["hard_only"]["allocation_delta"]
    base_hard = eval_rows["base_geometry_option"]["hard_only"]["allocation_delta"]
    geom_hard = eval_rows["geometry_conditioned"]["hard_only"]["allocation_delta"]
    calibrated_full = eval_rows["calibrated"]["full"]["allocation_delta"]
    base_full = eval_rows["base_geometry_option"]["full"]["allocation_delta"]
    hard_beats_base = float(calibrated_hard["observed"]) < float(base_hard["observed"])
    hard_beats_geometry = float(calibrated_hard["observed"]) < float(geom_hard["observed"])
    hard_closes = float(calibrated_hard["high"]) < 0.0
    full_beats_base = float(calibrated_full["observed"]) < float(base_full["observed"])
    if hard_closes:
        verdict = (
            "Calibration transform closes the hard-only allocation slice under the current diagnostic; this requires independent validation."
        )
    elif hard_beats_base and not hard_beats_geometry:
        verdict = (
            "Calibration transform improves over the raw geometry-option scorer on the hard slice, but it does not beat append-only geometry."
        )
    elif hard_beats_geometry:
        verdict = (
            "Calibration transform improves hard-only observed damage relative to append-only geometry, but the hard-only interval remains open."
        )
    else:
        verdict = (
            "Calibration transform does not improve the hard-only allocation boundary relative to the raw geometry-option scorer."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_calibration_transform",
        "device": str(device),
        "raw_score_source": "deterministic fi-064 geometry-option scorer regenerated with the same seed/config",
        "feature_dims": feature_dims,
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "transform_family_count": int(len(candidates)),
        },
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_split["episode"])),
            "hard_eval_anchors": int(np.sum(np.isin(eval_split["episode"], np.asarray(hard_episodes, dtype=np.int64)))),
        },
        "raw_model_selection": raw_selection,
        "selection": {
            "selected": transform_selection["selected"],
            "selection_key": transform_selection["selection_key"],
            "calibration_selected": transform_selection["calibration"][transform_selection["selected"]],
        },
        "eval": eval_rows,
        "diagnosis": {
            "hard_beats_raw_geometry_option_observed": bool(hard_beats_base),
            "hard_beats_geometry_conditioned_observed": bool(hard_beats_geometry),
            "hard_closes": bool(hard_closes),
            "full_beats_raw_geometry_option_observed": bool(full_beats_base),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "raw_score": "fi-064 scorer is regenerated deterministically from train labels and calibration selection; eval labels are not used for raw-score training or selection",
            "transform_selection": "transform family is selected on calibration exact-budget allocation only",
            "eval_targets": "eval option_error is used only after the calibrated score is fixed",
            "hard_ids": "held-out hard episode ids are used only for final diagnostic slicing",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["independent export validation", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        raw_geometry_option_score=eval_score.astype(np.float64),
        calibrated_score=calibrated_score.astype(np.float64),
        geometry_conditioned_score=geometry_conditioned.astype(np.float64),
        geometry_regime_weighted_score=geometry_regime_weighted.astype(np.float64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
