from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_candidate_oracle_gap as oracle_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_geometry_option_conditioned_allocation as option_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_direct_oracle_value.json"
DEFAULT_MD = REPORT_DIR / "state_generation_direct_oracle_value.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_direct_oracle_value_predictions.npz"
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


def tail_weight(split: dict[str, np.ndarray], threshold: float) -> np.ndarray:
    uniform = split["uniform_error"].astype(np.float64)
    risk = (uniform >= float(threshold)).astype(np.float64)
    return (1.0 + 0.75 * risk).astype(np.float64)


def target_matrices(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
) -> dict[str, dict[str, np.ndarray]]:
    train_tail_threshold = float(np.quantile(train["uniform_error"].astype(np.float64), 0.75))

    def oracle_regret(split: dict[str, np.ndarray]) -> np.ndarray:
        option_error = split["option_error"].astype(np.float64)
        return (option_error - np.min(option_error, axis=1, keepdims=True)).astype(np.float64)

    def uniform_relative_cost(split: dict[str, np.ndarray]) -> np.ndarray:
        option_error = split["option_error"].astype(np.float64)
        return (option_error - split["uniform_error"].astype(np.float64)[:, None]).astype(np.float64)

    def tail_weighted_error(split: dict[str, np.ndarray]) -> np.ndarray:
        option_error = split["option_error"].astype(np.float64)
        return (option_error * tail_weight(split, train_tail_threshold)[:, None]).astype(np.float64)

    builders = {
        "direct_option_error": lambda split: split["option_error"].astype(np.float64),
        "oracle_relative_regret": oracle_regret,
        "uniform_relative_cost": uniform_relative_cost,
        "tail_weighted_option_error": tail_weighted_error,
    }
    return {
        name: {
            "train": fn(train),
            "calibration": fn(cal),
            "eval": fn(eval_split),
        }
        for name, fn in builders.items()
    }


def train_direct_row(
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
        "# State-Generation Direct Oracle-Value Audit",
        "",
        f"- device: `{report['device']}`",
        f"- direct target count: `{len(report['direct_rows'])}`",
        f"- best direct row: `{report['diagnosis']['best_direct_row']}`",
        f"- best existing candidate: `{report['diagnosis']['best_existing_candidate']}`",
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
    parser = argparse.ArgumentParser(description="Train direct option-conditioned oracle-value targets and audit hard oracle headroom capture")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=1009)
    parser.add_argument("--epochs", type=int, default=120)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=6.0e-4)
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
    train_x = option_alloc.expand_option_features(features["train"], features["train_env"], depths)
    cal_x = option_alloc.expand_option_features(features["calibration"], features["calibration_env"], depths)
    eval_x = option_alloc.expand_option_features(features["eval"], features["eval_env"], depths)

    targets = target_matrices(train, cal, eval_split)
    direct_scores: dict[str, np.ndarray] = {}
    training_rows: dict[str, Any] = {}
    for index, (name, target) in enumerate(targets.items()):
        score, train_report = train_direct_row(
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
        direct_scores[name] = score
        training_rows[name] = train_report

    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    oracle_score = eval_split["option_error"].astype(np.float64)
    direct_summaries = {
        name: oracle_gap.summarize_candidate(
            eval_split,
            score,
            oracle_score,
            hard_mask,
            seed=int(args.seed) + index * 100000,
            samples=int(args.bootstrap_samples),
        )
        for index, (name, score) in enumerate(direct_scores.items())
    }
    existing_candidates = oracle_gap.load_candidates(eval_split)
    existing_summaries = {
        name: oracle_gap.summarize_candidate(
            eval_split,
            score,
            oracle_score,
            hard_mask,
            seed=int(args.seed) + 500000 + index * 100000,
            samples=int(args.bootstrap_samples),
        )
        for index, (name, score) in enumerate(sorted(existing_candidates.items()))
    }

    direct_ranking = [
        {"row": name, **payload["summary"]}
        for name, payload in direct_summaries.items()
    ]
    existing_ranking = [
        {"row": name, **payload["summary"]}
        for name, payload in existing_summaries.items()
    ]
    direct_ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    existing_ranking.sort(key=lambda item: (-float(item["mean_capture_ratio"]), float(item["mean_regret_to_oracle"])))
    best_direct = direct_ranking[0]
    best_existing = existing_ranking[0] if existing_ranking else {
        "row": "",
        "mean_capture_ratio": 0.0,
        "budget3_capture_ratio": 0.0,
        "budget4_capture_ratio": 0.0,
        "mean_regret_to_oracle": 0.0,
    }
    direct_closes = bool(float(best_direct["mean_capture_ratio"]) >= 0.5 and float(best_direct["budget4_capture_ratio"]) > 0.0)
    direct_beats_existing = bool(float(best_direct["mean_capture_ratio"]) > float(best_existing["mean_capture_ratio"]))
    budget3_beats_existing = bool(float(best_direct["budget3_capture_ratio"]) > float(best_existing["budget3_capture_ratio"]))
    if direct_closes:
        verdict = (
            "A direct option-conditioned oracle-value target captures a substantial share of the hard oracle ceiling. "
            "This is still a single-export learned result and requires independent export validation before any policy claim."
        )
    elif direct_beats_existing or budget3_beats_existing:
        verdict = (
            "Direct option-conditioned oracle-value training improves at least one oracle-headroom gap statistic over the "
            "existing fixed-candidate pool, but it does not close the hard budget-stress boundary."
        )
    else:
        verdict = (
            "Direct option-conditioned oracle-value targets do not outperform the existing fixed-candidate pool on the "
            "hard oracle-headroom audit. The missing object remains a stronger option-conditioned compute-value mechanism, "
            "not another evaluation-time score selector."
        )

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_direct_oracle_value",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
            "budget_multipliers": [2, 3, 4],
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta, then training loss",
        },
        "feature_dims": {
            **feature_dims,
            "expanded_option_feature_dim": int(train_x.shape[1]),
        },
        "hard_episode_union": hard_episodes,
        "direct_rows": training_rows,
        "direct_summaries": direct_summaries,
        "existing_candidate_count": int(len(existing_candidates)),
        "existing_ranking_top": existing_ranking[:8],
        "ranking": direct_ranking,
        "diagnosis": {
            "direct_oracle_value_closes": direct_closes,
            "direct_beats_existing_mean_capture": direct_beats_existing,
            "direct_beats_existing_budget3_capture": budget3_beats_existing,
            "best_direct_row": str(best_direct["row"]),
            "best_direct_mean_capture_ratio": clean_float(float(best_direct["mean_capture_ratio"])),
            "best_direct_budget3_capture_ratio": clean_float(float(best_direct["budget3_capture_ratio"])),
            "best_direct_budget4_capture_ratio": clean_float(float(best_direct["budget4_capture_ratio"])),
            "best_direct_mean_regret_to_oracle": clean_float(float(best_direct["mean_regret_to_oracle"])),
            "best_existing_candidate": str(best_existing["row"]),
            "best_existing_mean_capture_ratio": clean_float(float(best_existing["mean_capture_ratio"])),
            "best_existing_budget3_capture_ratio": clean_float(float(best_existing["budget3_capture_ratio"])),
            "best_existing_budget4_capture_ratio": clean_float(float(best_existing["budget4_capture_ratio"])),
            "best_existing_mean_regret_to_oracle": clean_float(float(best_existing["mean_regret_to_oracle"])),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x, explicit environment geometry, candidate depth token, and geometry-option interactions",
            "training_targets": "train split option_error transforms only",
            "selection": "calibration split metrics only; held-out hard ids are not used for training or model selection",
            "oracle_scope": "eval option_error is used only after fixed scores are generated to measure hard oracle regret and capture",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": [
            "deployable allocation policy",
            "independent export validation",
            "complete BEDC-native world model",
            "evaluation-option-error training",
        ],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        **{f"{name}_score": score.astype(np.float64) for name, score in direct_scores.items()},
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
