from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured
import _state_generation_candidate_oracle_gap as oracle_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_mechanism_conditioned_value as mech_value
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_geometry_option_conditioned_allocation as option_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_budget_replacement_value.json"
DEFAULT_MD = REPORT_DIR / "state_generation_budget_replacement_value.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_budget_replacement_value_predictions.npz"
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


def exact_cost_for_episode(option_score: np.ndarray, depths: np.ndarray, target: int) -> float:
    n = option_score.shape[0]
    dp = np.full((n + 1, target + 1), np.inf, dtype=np.float64)
    dp[0, 0] = 0.0
    for row in range(n):
        for budget in range(target + 1):
            base = dp[row, budget]
            if not math.isfinite(float(base)):
                continue
            for col, depth in enumerate(depths.astype(np.int64)):
                new_budget = budget + int(depth)
                if new_budget <= target:
                    value = base + float(option_score[row, col])
                    if value < dp[row + 1, new_budget]:
                        dp[row + 1, new_budget] = value
    out = float(dp[n, target])
    if not math.isfinite(out):
        raise RuntimeError("infeasible exact-budget episode")
    return out


def replacement_targets(split: dict[str, np.ndarray], depths: np.ndarray, multiplier: int) -> np.ndarray:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    out = np.zeros_like(option_error, dtype=np.float64)
    infeasible_penalty = float(np.max(option_error) - np.min(option_error) + 1.0)
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        local = option_error[idx]
        target = int(multiplier * len(idx))
        base_cost = exact_cost_for_episode(local, depths, target)
        for local_row, global_row in enumerate(idx):
            for col, depth in enumerate(depths.astype(np.int64)):
                residual_target = target - int(depth)
                if residual_target < 0:
                    out[global_row, col] = np.max(local) + 1.0
                    continue
                residual = np.delete(local, local_row, axis=0)
                if len(residual) == 0:
                    residual_cost = 0.0 if residual_target == 0 else np.inf
                else:
                    try:
                        residual_cost = exact_cost_for_episode(residual, depths, residual_target)
                    except RuntimeError:
                        residual_cost = np.inf
                forced_cost = float(local[local_row, col]) + float(residual_cost)
                out[global_row, col] = forced_cost - base_cost if math.isfinite(forced_cost) else infeasible_penalty
    return out.astype(np.float64)


def target_rows(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
    depths: np.ndarray,
) -> dict[str, dict[str, np.ndarray]]:
    del eval_split
    return {
        "replacement_budget2": {
            "train": replacement_targets(train, depths, 2),
            "calibration": replacement_targets(cal, depths, 2),
        },
        "replacement_budget3": {
            "train": replacement_targets(train, depths, 3),
            "calibration": replacement_targets(cal, depths, 3),
        },
        "replacement_budget4": {
            "train": replacement_targets(train, depths, 4),
            "calibration": replacement_targets(cal, depths, 4),
        },
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


def prepare_features(data: dict[str, np.ndarray], latents: dict[str, np.ndarray], depths: np.ndarray) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    features, feature_dims = geometry_alloc.augment_features(data, latents)
    train_mech = mech_value.rollout_option_features(data, "train", depths)
    cal_mech = mech_value.rollout_option_features(data, "calibration", depths)
    eval_mech = mech_value.rollout_option_features(data, "eval", depths)
    mean, scale = mech_value.fit_standardizer(train_mech.reshape(-1, train_mech.shape[2]))
    train_mech_z = mech_value.apply_standardizer(train_mech.reshape(-1, train_mech.shape[2]), mean, scale).reshape(train_mech.shape)
    cal_mech_z = mech_value.apply_standardizer(cal_mech.reshape(-1, cal_mech.shape[2]), mean, scale).reshape(cal_mech.shape)
    eval_mech_z = mech_value.apply_standardizer(eval_mech.reshape(-1, eval_mech.shape[2]), mean, scale).reshape(eval_mech.shape)
    return {
        "train": mech_value.expand_mechanism_features(features["train"], features["train_env"], train_mech_z, depths),
        "calibration": mech_value.expand_mechanism_features(features["calibration"], features["calibration_env"], cal_mech_z, depths),
        "eval": mech_value.expand_mechanism_features(features["eval"], features["eval_env"], eval_mech_z, depths),
    }, {
        **feature_dims,
        "mechanism_feature_dim": int(train_mech.shape[2]),
        "expanded_mechanism_feature_dim": int(
            mech_value.expand_mechanism_features(features["train"][:1], features["train_env"][:1], train_mech_z[:1], depths).shape[1]
        ),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Budget Replacement-Value Audit",
        "",
        f"- device: `{report['device']}`",
        f"- best replacement row: `{report['diagnosis']['best_replacement_row']}`",
        f"- best mechanism row: `{report['diagnosis']['best_mechanism_row']}`",
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
    parser = argparse.ArgumentParser(description="Train budget-aware forced-replacement value rows against hard oracle ceiling")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--mechanism-report", default=str(REPORT_DIR / "state_generation_mechanism_conditioned_value.json"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=1223)
    parser.add_argument("--epochs", type=int, default=70)
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
    if not np.array_equal(depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {depths} vs {structured.DEPTHS}")
    features, feature_dims = prepare_features(data, latents, depths)
    targets = target_rows(train, cal, eval_split, depths)

    scores: dict[str, np.ndarray] = {}
    training: dict[str, Any] = {}
    for index, (name, target) in enumerate(targets.items()):
        score, report = train_row(
            name,
            target,
            features["train"],
            features["calibration"],
            features["eval"],
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
        training[name] = report

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
    mechanism_report = json.loads(Path(args.mechanism_report).read_text(encoding="utf-8"))
    mechanism_diag = mechanism_report.get("diagnosis", {})
    mechanism_row = str(mechanism_diag.get("best_mechanism_row", ""))
    mechanism_mean = float(mechanism_diag.get("best_mechanism_mean_capture_ratio", 0.0))
    mechanism_budget3 = float(mechanism_diag.get("best_mechanism_budget3_capture_ratio", 0.0))
    replacement_closes = bool(float(best["mean_capture_ratio"]) >= 0.5 and float(best["budget4_capture_ratio"]) > 0.0)
    beats_mechanism_mean = bool(float(best["mean_capture_ratio"]) > mechanism_mean)
    beats_mechanism_budget3 = bool(float(best["budget3_capture_ratio"]) > mechanism_budget3)
    if replacement_closes:
        verdict = (
            "Budget-aware forced-replacement value captures a substantial share of hard oracle headroom. "
            "Independent export validation is still required."
        )
    elif beats_mechanism_mean or beats_mechanism_budget3:
        verdict = (
            "Budget-aware forced-replacement targets improve at least one hard oracle-gap statistic over passive "
            "mechanism-conditioned features, but allocation closure remains open."
        )
    else:
        verdict = (
            "Budget-aware forced-replacement targets do not improve over passive mechanism-conditioned features. "
            "The hard allocation bottleneck remains unresolved."
        )

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_budget_replacement_value",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
            "target_multipliers": [2, 3, 4],
        },
        "feature_dims": feature_dims,
        "hard_episode_union": hard_episodes,
        "training": training,
        "summaries": summaries,
        "ranking": ranking,
        "diagnosis": {
            "budget_replacement_closes": replacement_closes,
            "replacement_beats_mechanism_mean_capture": beats_mechanism_mean,
            "replacement_beats_mechanism_budget3_capture": beats_mechanism_budget3,
            "best_replacement_row": str(best["row"]),
            "best_replacement_mean_capture_ratio": clean_float(float(best["mean_capture_ratio"])),
            "best_replacement_budget3_capture_ratio": clean_float(float(best["budget3_capture_ratio"])),
            "best_replacement_budget4_capture_ratio": clean_float(float(best["budget4_capture_ratio"])),
            "best_replacement_mean_regret_to_oracle": clean_float(float(best["mean_regret_to_oracle"])),
            "best_mechanism_row": mechanism_row,
            "best_mechanism_mean_capture_ratio": clean_float(mechanism_mean),
            "best_mechanism_budget3_capture_ratio": clean_float(mechanism_budget3),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x, geometry, predicted rollout mechanism summaries, and option interactions",
            "training_targets": "train/cal split forced-replacement exact-budget values derived only from their own option_error",
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
