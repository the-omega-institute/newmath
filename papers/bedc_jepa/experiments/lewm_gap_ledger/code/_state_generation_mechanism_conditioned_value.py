from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_candidate_oracle_gap as oracle_gap
import _state_generation_direct_oracle_value as direct_value
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_geometry_option_conditioned_allocation as option_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_mechanism_conditioned_value.json"
DEFAULT_MD = REPORT_DIR / "state_generation_mechanism_conditioned_value.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_mechanism_conditioned_value_predictions.npz"
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


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def rollout_option_features(data: dict[str, np.ndarray], split: str, depths: np.ndarray) -> np.ndarray:
    current = data[f"{split}_current_z"].astype(np.float32)
    pred = data[f"{split}_pred_z"].astype(np.float32)
    valid = data[f"{split}_pred_z_valid"].astype(np.float32)
    n = current.shape[0]
    out = np.zeros((n, len(depths), 12), dtype=np.float32)
    for depth_index, depth_value in enumerate(depths.astype(np.int64)):
        d = int(depth_value)
        prefix = pred[:, :d, :]
        prefix_valid = valid[:, :d]
        final = pred[:, d - 1, :]
        points = np.concatenate([current[:, None, :], prefix], axis=1)
        steps = points[:, 1:, :] - points[:, :-1, :]
        step_norm = np.linalg.norm(steps.astype(np.float32), axis=2)
        final_delta = final - current
        final_delta_norm = np.linalg.norm(final_delta.astype(np.float32), axis=1)
        if d > 1:
            second = points[:, 2:, :] - 2.0 * points[:, 1:-1, :] + points[:, :-2, :]
            curvature = np.linalg.norm(second.astype(np.float32), axis=2)
            curvature_mean = np.mean(curvature, axis=1)
            curvature_max = np.max(curvature, axis=1)
        else:
            curvature_mean = np.zeros(n, dtype=np.float32)
            curvature_max = np.zeros(n, dtype=np.float32)
        mean_prefix = np.mean(prefix, axis=1)
        final_to_mean = np.linalg.norm((final - mean_prefix).astype(np.float32), axis=1)
        step_mean = np.mean(step_norm, axis=1)
        step_std = np.std(step_norm, axis=1)
        step_max = np.max(step_norm, axis=1)
        step_last = step_norm[:, -1]
        step_energy = np.sum(step_norm, axis=1)
        valid_fraction = np.mean(prefix_valid, axis=1)
        final_valid = prefix_valid[:, -1]
        instability = step_std / (step_mean + 1.0e-6)
        out[:, depth_index, :] = np.stack(
            [
                final_delta_norm,
                final_delta_norm / float(d),
                step_mean,
                step_std,
                step_max,
                step_last,
                step_energy,
                curvature_mean,
                curvature_max,
                final_to_mean,
                valid_fraction,
                final_valid,
            ],
            axis=1,
        ).astype(np.float32)
        out[:, depth_index, -1] = np.where(np.isfinite(out[:, depth_index, -1]), out[:, depth_index, -1], 0.0)
        out[:, depth_index, -2] = np.where(np.isfinite(out[:, depth_index, -2]), out[:, depth_index, -2], 0.0)
        out[:, depth_index, 3] = np.where(np.isfinite(out[:, depth_index, 3]), out[:, depth_index, 3], 0.0)
        out[:, depth_index, :] = np.where(np.isfinite(out[:, depth_index, :]), out[:, depth_index, :], 0.0)
        out[:, depth_index, 3] = instability.astype(np.float32)
    return out.astype(np.float32)


def expand_mechanism_features(
    base_x: np.ndarray,
    env_z: np.ndarray,
    mechanism_z: np.ndarray,
    depths: np.ndarray,
) -> np.ndarray:
    opt = option_alloc.option_features(depths).astype(np.float32)
    rows = np.repeat(base_x.astype(np.float32), len(depths), axis=0)
    env = np.repeat(env_z.astype(np.float32), len(depths), axis=0)
    tiled_opt = np.tile(opt, (len(base_x), 1)).astype(np.float32)
    mechanism = mechanism_z.reshape(len(base_x) * len(depths), mechanism_z.shape[2]).astype(np.float32)
    env_interaction = (env[:, :, None] * tiled_opt[:, None, :]).reshape(len(rows), -1).astype(np.float32)
    mechanism_interaction = (mechanism[:, :, None] * tiled_opt[:, None, :]).reshape(len(rows), -1).astype(np.float32)
    return np.concatenate([rows, tiled_opt, env_interaction, mechanism, mechanism_interaction], axis=1).astype(np.float32)


def target_rows(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
) -> dict[str, dict[str, np.ndarray]]:
    all_targets = direct_value.target_matrices(train, cal, eval_split)
    return {
        "mechanism_option_error": all_targets["direct_option_error"],
        "mechanism_uniform_relative_cost": all_targets["uniform_relative_cost"],
    }


def train_row(
    name: str,
    targets: dict[str, np.ndarray],
    train_x: np.ndarray,
    cal_x: np.ndarray,
    eval_x: np.ndarray,
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
    depths: np.ndarray,
    *,
    device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    batch: int,
    lr: float,
) -> tuple[np.ndarray, dict[str, Any]]:
    train_target = targets["train"].astype(np.float64)
    y_mean = float(np.mean(train_target.reshape(-1)))
    y_scale = float(np.std(train_target.reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    train_target_std = ((train_target.reshape(-1) - y_mean) / y_scale).astype(np.float32)
    model, selection = option_alloc.train_model(
        train_x,
        train_target_std,
        train_target,
        cal_x,
        cal,
        depths,
        y_mean,
        y_scale,
        device=device,
        seed=int(seed),
        hidden=int(hidden),
        depth=int(depth),
        epochs=int(epochs),
        batch=int(batch),
        lr=float(lr),
    )
    eval_score = option_alloc.reshape_scores(
        option_alloc.predict(model, eval_x, device, int(batch)) * y_scale + y_mean,
        len(eval_split["episode"]),
        depths,
    )
    return eval_score.astype(np.float64), {
        "name": name,
        "target_mean": clean_float(y_mean),
        "target_scale": clean_float(y_scale),
        "selection": selection,
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Mechanism-Conditioned Value Audit",
        "",
        f"- device: `{report['device']}`",
        f"- mechanism feature dim: `{report['feature_dims']['mechanism_feature_dim']}`",
        f"- best mechanism row: `{report['diagnosis']['best_mechanism_row']}`",
        f"- best direct row: `{report['diagnosis']['best_direct_row']}`",
        "",
        "| row | mean capture | budget-3 capture | budget-4 capture | mean regret |",
        "|---|---:|---:|---:|---:|",
    ]
    for row in report["ranking"]:
        lines.append(
            f"| `{row['row']}` | {row['mean_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | "
            f"{row['mean_regret_to_oracle']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train mechanism-conditioned option-value rows against hard oracle ceiling")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--direct-report", default=str(REPORT_DIR / "state_generation_direct_oracle_value.json"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=1117)
    parser.add_argument("--epochs", type=int, default=90)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=5.0e-4)
    parser.add_argument("--bootstrap-samples", type=int, default=4000)
    args = parser.parse_args()

    start_time = time.time()
    device = option_alloc.configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    features, feature_dims = geometry_alloc.augment_features(data, latents)

    train_mech = rollout_option_features(data, "train", depths)
    cal_mech = rollout_option_features(data, "calibration", depths)
    eval_mech = rollout_option_features(data, "eval", depths)
    mech_mean, mech_scale = fit_standardizer(train_mech.reshape(-1, train_mech.shape[2]))
    train_mech_z = apply_standardizer(train_mech.reshape(-1, train_mech.shape[2]), mech_mean, mech_scale).reshape(train_mech.shape)
    cal_mech_z = apply_standardizer(cal_mech.reshape(-1, cal_mech.shape[2]), mech_mean, mech_scale).reshape(cal_mech.shape)
    eval_mech_z = apply_standardizer(eval_mech.reshape(-1, eval_mech.shape[2]), mech_mean, mech_scale).reshape(eval_mech.shape)

    train_x = expand_mechanism_features(features["train"], features["train_env"], train_mech_z, depths)
    cal_x = expand_mechanism_features(features["calibration"], features["calibration_env"], cal_mech_z, depths)
    eval_x = expand_mechanism_features(features["eval"], features["eval_env"], eval_mech_z, depths)

    scores: dict[str, np.ndarray] = {}
    training: dict[str, Any] = {}
    for index, (name, target) in enumerate(target_rows(train, cal, eval_split).items()):
        score, train_report = train_row(
            name,
            target,
            train_x,
            cal_x,
            eval_x,
            train,
            cal,
            eval_split,
            depths,
            device=device,
            seed=int(args.seed) + index * 10000,
            hidden=int(args.hidden),
            depth=int(args.depth),
            epochs=int(args.epochs),
            batch=int(args.batch),
            lr=float(args.lr),
        )
        scores[name] = score
        training[name] = train_report

    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    oracle_score = eval_split["option_error"].astype(np.float64)
    summaries = {
        name: oracle_gap.summarize_candidate(
            eval_split,
            score,
            oracle_score,
            hard_mask,
            seed=int(args.seed) + index * 100000,
            samples=int(args.bootstrap_samples),
        )
        for index, (name, score) in enumerate(scores.items())
    }
    ranking = [{"row": name, **payload["summary"]} for name, payload in summaries.items()]
    ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    best = ranking[0]
    direct_report = json.loads(Path(args.direct_report).read_text(encoding="utf-8"))
    direct_diag = direct_report.get("diagnosis", {})
    direct_mean = float(direct_diag.get("best_direct_mean_capture_ratio", 0.0))
    direct_budget3 = float(direct_diag.get("best_direct_budget3_capture_ratio", 0.0))
    direct_row = str(direct_diag.get("best_direct_row", ""))
    mechanism_closes = bool(float(best["mean_capture_ratio"]) >= 0.5 and float(best["budget4_capture_ratio"]) > 0.0)
    beats_direct_mean = bool(float(best["mean_capture_ratio"]) > direct_mean)
    beats_direct_budget3 = bool(float(best["budget3_capture_ratio"]) > direct_budget3)
    if mechanism_closes:
        verdict = (
            "Mechanism-conditioned rollout features capture a substantial share of hard oracle headroom. "
            "This remains a single-export result requiring independent validation."
        )
    elif beats_direct_mean or beats_direct_budget3:
        verdict = (
            "Mechanism-conditioned rollout features improve at least one direct oracle-value gap statistic, "
            "but the hard oracle-headroom boundary remains open."
        )
    else:
        verdict = (
            "Mechanism-conditioned rollout features do not improve over the direct oracle-value target baseline. "
            "The hard allocation bottleneck remains a mechanism-learning problem rather than a feature append alone."
        )

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_mechanism_conditioned_value",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
            "targets": list(scores.keys()),
        },
        "feature_dims": {
            **feature_dims,
            "mechanism_feature_dim": int(train_mech.shape[2]),
            "expanded_mechanism_feature_dim": int(train_x.shape[1]),
        },
        "hard_episode_union": hard_episodes,
        "training": training,
        "summaries": summaries,
        "ranking": ranking,
        "diagnosis": {
            "mechanism_conditioned_closes": mechanism_closes,
            "mechanism_beats_direct_mean_capture": beats_direct_mean,
            "mechanism_beats_direct_budget3_capture": beats_direct_budget3,
            "best_mechanism_row": str(best["row"]),
            "best_mechanism_mean_capture_ratio": clean_float(float(best["mean_capture_ratio"])),
            "best_mechanism_budget3_capture_ratio": clean_float(float(best["budget3_capture_ratio"])),
            "best_mechanism_budget4_capture_ratio": clean_float(float(best["budget4_capture_ratio"])),
            "best_mechanism_mean_regret_to_oracle": clean_float(float(best["mean_regret_to_oracle"])),
            "best_direct_row": direct_row,
            "best_direct_mean_capture_ratio": clean_float(direct_mean),
            "best_direct_budget3_capture_ratio": clean_float(direct_budget3),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x, explicit environment geometry, candidate depth token, predicted rollout transition/curvature/validity summaries, and option interactions",
            "training_targets": "train split option_error transforms only",
            "selection": "calibration split metrics only; held-out hard ids are not used for training or model selection",
            "oracle_scope": "eval option_error is used only after fixed scores are generated to measure hard oracle regret and capture",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": [
            "deployable allocation policy",
            "independent export validation",
            "complete BEDC-native world model",
            "prediction parity",
        ],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        **{f"{name}_score": score.astype(np.float64) for name, score in scores.items()},
    )
    Path(args.json).write_text(
        json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
