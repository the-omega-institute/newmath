from __future__ import annotations

import argparse
import json
import math
import os
import random
import time
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch

import _compute_value_structured_assignment as structured
import _state_generation_episode_allocation as episode_alloc
import _state_generation_environment_state_descriptors as env_desc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_LATENTS = Path("C:/OMEGA/le-wm-survey/tworooms_latent_large.npz")
DEFAULT_JSON = REPORT_DIR / "state_generation_geometry_conditioned_allocation.json"
DEFAULT_MD = REPORT_DIR / "state_generation_geometry_conditioned_allocation.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_geometry_conditioned_allocation_predictions.npz"
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


def configure(seed: int) -> torch.device:
    os.environ["PYTHONHASHSEED"] = str(seed)
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def env_feature_matrix(aligned: dict[str, np.ndarray], latents: dict[str, np.ndarray], split: str) -> np.ndarray:
    rows = env_desc.anchor_env_rows(aligned, latents, split)
    names = [
        "distance_to_target",
        "distance_change",
        "agent_x",
        "agent_y",
        "target_x",
        "target_y",
        "relative_x",
        "relative_y",
        "same_room",
        "different_room",
        "agent_room",
        "target_room",
        "crosses_room_midline",
        "action_norm",
        "action_delta",
        "transition_step",
    ]
    return np.stack([rows[name].astype(np.float64) for name in names], axis=1).astype(np.float32)


def augment_features(
    data: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    train_x_mean, train_x_scale = standardizer(data["train_x"].astype(np.float32))
    train_x = apply_standardizer(data["train_x"], train_x_mean, train_x_scale)
    cal_x = apply_standardizer(data["calibration_x"], train_x_mean, train_x_scale)
    eval_x = apply_standardizer(data["eval_x"], train_x_mean, train_x_scale)
    train_env = env_feature_matrix(data, latents, "train")
    cal_env = env_feature_matrix(data, latents, "calibration")
    eval_env = env_feature_matrix(data, latents, "eval")
    env_mean, env_scale = standardizer(train_env)
    train_env_z = apply_standardizer(train_env, env_mean, env_scale)
    cal_env_z = apply_standardizer(cal_env, env_mean, env_scale)
    eval_env_z = apply_standardizer(eval_env, env_mean, env_scale)
    return {
        "train": np.concatenate([train_x, train_env_z], axis=1).astype(np.float32),
        "calibration": np.concatenate([cal_x, cal_env_z], axis=1).astype(np.float32),
        "eval": np.concatenate([eval_x, eval_env_z], axis=1).astype(np.float32),
        "train_env": train_env_z,
        "calibration_env": cal_env_z,
        "eval_env": eval_env_z,
    }, {
        "base_feature_dim": int(train_x.shape[1]),
        "geometry_feature_dim": int(train_env_z.shape[1]),
        "augmented_feature_dim": int(train_x.shape[1] + train_env_z.shape[1]),
    }


def slice_eval(split: dict[str, np.ndarray], mask: np.ndarray) -> dict[str, np.ndarray]:
    rows = np.where(mask.astype(bool))[0].astype(np.int64)
    return {
        "x": split["x"][rows] if "x" in split else np.zeros((len(rows), 0), dtype=np.float32),
        "episode": split["episode"][rows].astype(np.int64),
        "anchor_ep_t0": split["anchor_ep_t0"][rows].astype(np.int64),
        "option_error": split["option_error"][rows].astype(np.float64),
        "uniform_error": split["uniform_error"][rows].astype(np.float64),
        "true_mv": split["true_mv"][rows].astype(np.float64),
    }


def evaluate_slice(split: dict[str, np.ndarray], score: np.ndarray, mask: np.ndarray, *, seed: int) -> dict[str, Any]:
    local = slice_eval(split, mask)
    local_score = score[mask.astype(bool)].astype(np.float64)
    return episode_alloc.evaluate(local, local_score, seed=seed)


def load_reference_rows() -> dict[str, np.ndarray]:
    return {
        "episode_best_seed": load_npz(REPORT_DIR / "state_generation_episode_allocation_seed_617_predictions.npz")[
            "episode_allocation_score"
        ].astype(np.float64),
        "episode_objective": load_npz(REPORT_DIR / "state_generation_episode_allocation_predictions.npz")[
            "episode_allocation_score"
        ].astype(np.float64),
        "seed_mean": load_npz(REPORT_DIR / "state_generation_episode_seed_ensemble_predictions.npz")[
            "mean_score"
        ].astype(np.float64),
    }


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
            slice_name: evaluate_slice(eval_split, score, mask, seed=seed + row_idx * 97 + slice_idx * 13)
            for slice_idx, (slice_name, mask) in enumerate(masks.items())
        }
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Geometry-Conditioned Allocation",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        f"- geometry feature dim: `{report['feature_dims']['geometry_feature_dim']}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high |",
        "|---|---:|---:|---:|---:|",
    ]
    for name in ["geometry_conditioned", "episode_best_seed", "episode_objective", "seed_mean"]:
        row = report["eval"][name]
        full = row["full"]["allocation_delta"]
        non_hard = row["non_hard"]["allocation_delta"]
        hard = row["hard_only"]["allocation_delta"]
        lines.append(
            f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | "
            f"{hard['observed']:.6g} | {hard['high']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an episode allocation model with explicit geometry conditioning")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--seed", type=int, default=631)
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=128)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    option_depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(option_depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {option_depths} vs {structured.DEPTHS}")
    features, feature_dims = augment_features(data, latents)
    train_oracle = episode_alloc.oracle_choice(train)
    model, selection = episode_alloc.train_model(
        features["train"],
        episode_alloc.centered_errors(train["option_error"]),
        train_oracle,
        features["calibration"],
        cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    eval_score = episode_alloc.predict(model, features["eval"], device, int(args.batch))
    rows = {"geometry_conditioned": eval_score}
    rows.update(load_reference_rows())
    eval_rows = evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 4000)
    geom_hard = eval_rows["geometry_conditioned"]["hard_only"]["allocation_delta"]
    best_hard = eval_rows["episode_best_seed"]["hard_only"]["allocation_delta"]
    geom_full = eval_rows["geometry_conditioned"]["full"]["allocation_delta"]
    episode_full = eval_rows["episode_objective"]["full"]["allocation_delta"]
    verdict = (
        "Geometry conditioning improves the hard-only observed allocation delta relative to the best replicated seed, "
        "but it does not close hard-only allocation."
        if float(geom_hard["observed"]) < float(best_hard["observed"]) and float(geom_hard["high"]) >= 0.0
        else "Geometry conditioning does not improve the hard-only allocation boundary relative to the best replicated seed."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_geometry_conditioned_allocation",
        "device": str(device),
        "feature_dims": feature_dims,
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "seed": int(args.seed),
            "loss": "same episode exact-budget objective as state_generation_episode_allocation",
        },
        "counts": {
            "train": int(len(features["train"])),
            "calibration": int(len(features["calibration"])),
            "eval": int(len(features["eval"])),
            "hard_eval_anchors": int(np.sum(np.isin(eval_split["episode"], np.asarray(hard_episodes, dtype=np.int64)))),
        },
        "hard_episode_union": hard_episodes,
        "selection": selection,
        "eval": eval_rows,
        "diagnosis": {
            "full_beats_episode_objective_observed": bool(float(geom_full["observed"]) < float(episode_full["observed"])),
            "full_closes": bool(float(geom_full["high"]) < 0.0),
            "hard_beats_best_seed_observed": bool(float(geom_hard["observed"]) < float(best_hard["observed"])),
            "hard_closes": bool(float(geom_hard["high"]) < 0.0),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x plus explicit two-rooms state/action geometry from source latent export",
            "training_targets": "train option_error is converted to exact-budget oracle choices; hard eval ids are never used for training or calibration selection",
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta",
            "eval_targets": "eval option_error used only after fixed score generation for metrics",
            "source_latents": str(Path(args.latents)),
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=structured.DEPTHS.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        geometry_conditioned_score=eval_score.astype(np.float64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
