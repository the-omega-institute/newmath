from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_budget_conditioned_value as budget_value
import _state_generation_candidate_oracle_gap as oracle_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_hard_perturbation_value as hard_value
import _state_generation_mechanism_conditioned_value as mech_value


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_perturbation_value_learner.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_perturbation_value_learner.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
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


def forced_delta_targets(split: dict[str, np.ndarray], depths: np.ndarray, budgets: np.ndarray) -> dict[int, np.ndarray]:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    out = {int(budget): np.zeros_like(option_error, dtype=np.float64) for budget in budgets.astype(np.int64)}
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        local = option_error[idx]
        for budget in budgets.astype(np.int64):
            out[int(budget)][idx] = hard_value.forced_delta_labels(local, depths, int(budget) * len(idx))
    return out


def option_features(
    features: dict[str, np.ndarray],
    feature_dims: dict[str, Any],
    data: dict[str, np.ndarray],
    split: str,
    depths: np.ndarray,
) -> tuple[np.ndarray, dict[str, Any]]:
    mech = mech_value.rollout_option_features(data, split, depths)
    train_mech = mech_value.rollout_option_features(data, "train", depths)
    mean, scale = mech_value.fit_standardizer(train_mech.reshape(-1, train_mech.shape[2]))
    mech_z = mech_value.apply_standardizer(mech.reshape(-1, mech.shape[2]), mean, scale).reshape(mech.shape)
    expanded = mech_value.expand_mechanism_features(features[split], features[f"{split}_env"], mech_z, depths)
    return expanded.astype(np.float32), {
        **feature_dims,
        "mechanism_feature_dim": int(mech.shape[2]),
        "expanded_feature_dim": int(expanded.shape[1]),
    }


def expand_with_budgets(option_x: np.ndarray, n: int, depths: np.ndarray, budgets: np.ndarray) -> np.ndarray:
    return budget_value.expand_budget_conditioned_features(option_x, n, depths, budgets).astype(np.float32)


def flatten_targets(targets: dict[int, np.ndarray], budgets: np.ndarray) -> np.ndarray:
    return np.concatenate([targets[int(budget)].reshape(-1) for budget in budgets.astype(np.int64)], axis=0).astype(np.float64)


def hard_label_alignment(
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    budgets: np.ndarray,
    hard_episodes: list[int],
    scores: dict[int, np.ndarray],
) -> dict[str, Any]:
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    hard_split = geometry_alloc.slice_eval(split, hard_mask)
    hard_scores = {int(budget): scores[int(budget)][hard_mask] for budget in budgets.astype(np.int64)}
    targets = forced_delta_targets(hard_split, depths, budgets)
    rows: dict[str, Any] = {}
    rhos: list[float] = []
    for budget in budgets.astype(np.int64):
        rho = hard_value.spearman(hard_scores[int(budget)].reshape(-1), targets[int(budget)].reshape(-1))
        rows[f"budget_{int(budget)}"] = {
            "score_label_spearman": clean_float(rho),
            "label_iqr": clean_float(float(np.quantile(targets[int(budget)], 0.75) - np.quantile(targets[int(budget)], 0.25))),
            "predicted_score_iqr": clean_float(float(np.quantile(hard_scores[int(budget)], 0.75) - np.quantile(hard_scores[int(budget)], 0.25))),
        }
        rhos.append(float(rho))
    return {"rows": rows, "mean_score_label_spearman": clean_float(float(np.mean(rhos)))}


def summarize_hard_capture(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    hard_episodes: list[int],
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    hard_mask = np.isin(split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget_index, multiplier in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = oracle_gap.episode_values(split, oracle_score, hard_mask, int(multiplier))
        score_eps, score_values = oracle_gap.episode_values(split, scores[int(multiplier)], hard_mask, int(multiplier))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {multiplier}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{int(multiplier)}"] = {
            "score_delta": oracle_gap.bootstrap_mean(score_values, seed=seed + 1009 * budget_index, samples=samples),
            "oracle_delta": oracle_gap.bootstrap_mean(oracle_values, seed=seed + 1009 * budget_index + 17, samples=samples),
            "regret_to_oracle": oracle_gap.bootstrap_mean(regret, seed=seed + 1009 * budget_index + 31, samples=samples),
            "headroom_capture_ratio": clean_float(float(capture)),
        }
    return {
        "budgets": budgets,
        "summary": {
            "mean_capture_ratio": clean_float(float(np.mean(captures))),
            "min_capture_ratio": clean_float(float(np.min(captures))),
            "mean_regret_to_oracle": clean_float(float(np.mean(regrets))),
            "budget2_capture_ratio": clean_float(float(captures[0])),
            "budget3_capture_ratio": clean_float(float(captures[1])),
            "budget4_capture_ratio": clean_float(float(captures[2])),
        },
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    summary = report["diagnosis"]
    lines = [
        "# State-Generation Hard Perturbation-Value Learner",
        "",
        f"- device: `{report['device']}`",
        f"- mean hard label rho: `{summary['hard_mean_score_label_spearman']:.6g}`",
        f"- fixed-score baseline rho: `{summary['fixed_score_mean_score_label_spearman']:.6g}`",
        "",
        "| budget | label rho | capture | regret |",
        "|---|---:|---:|---:|",
    ]
    for budget in ["budget_2", "budget_3", "budget_4"]:
        rho = report["hard_label_alignment"]["rows"][budget]["score_label_spearman"]
        cap = report["hard_capture"]["budgets"][budget]["headroom_capture_ratio"]
        regret = report["hard_capture"]["budgets"][budget]["regret_to_oracle"]["observed"]
        lines.append(f"| `{budget}` | {rho:.6g} | {cap:.6g} | {regret:.6g} |")
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a budget-conditioned learner on exact-budget forced-option perturbation labels")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--fixed-score", default=str(REPORT_DIR / "state_generation_global_assignment_transfer_predictions.npz"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2027)
    parser.add_argument("--epochs", type=int, default=8)
    parser.add_argument("--hidden", type=int, default=128)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=1024)
    parser.add_argument("--lr", type=float, default=5.0e-4)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    start_time = time.time()
    device = budget_value.configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    features, feature_dims = geometry_alloc.augment_features(data, latents)
    train_x, feature_dims = option_features(features, feature_dims, data, "train", depths)
    cal_x, _ = option_features(features, feature_dims, data, "calibration", depths)
    eval_x, _ = option_features(features, feature_dims, data, "eval", depths)
    train_targets = forced_delta_targets(train, depths, BUDGETS)
    train_flat = flatten_targets(train_targets, BUDGETS)
    y_mean = float(np.mean(train_flat))
    y_scale = float(np.std(train_flat))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    train_y = ((train_flat - y_mean) / y_scale).astype(np.float32)
    train_budget_x = expand_with_budgets(train_x, len(train["episode"]), depths, BUDGETS)
    cal_budget_x = expand_with_budgets(cal_x, len(cal["episode"]), depths, BUDGETS)
    eval_budget_x = expand_with_budgets(eval_x, len(eval_split["episode"]), depths, BUDGETS)
    model, selection = budget_value.train_model(
        train_budget_x,
        train_y,
        cal_budget_x,
        cal,
        depths,
        BUDGETS,
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
    eval_flat = budget_value.predict(model, eval_budget_x, device, int(args.batch)) * y_scale + y_mean
    eval_scores = budget_value.reshape_budget_scores(eval_flat, len(eval_split["episode"]), depths, BUDGETS)
    fixed = load_npz(Path(args.fixed_score))
    fixed_scores = {int(budget): fixed[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    hard_alignment = hard_label_alignment(eval_split, depths, BUDGETS, hard_episodes, eval_scores)
    fixed_alignment = hard_label_alignment(eval_split, depths, BUDGETS, hard_episodes, fixed_scores)
    hard_capture = summarize_hard_capture(eval_split, eval_scores, hard_episodes, seed=int(args.seed) + 3000, samples=int(args.bootstrap_samples))
    fixed_capture = summarize_hard_capture(eval_split, fixed_scores, hard_episodes, seed=int(args.seed) + 5000, samples=int(args.bootstrap_samples))
    rho_gain = float(hard_alignment["mean_score_label_spearman"]) - float(fixed_alignment["mean_score_label_spearman"])
    capture_gain = float(hard_capture["summary"]["mean_capture_ratio"]) - float(fixed_capture["summary"]["mean_capture_ratio"])
    closes = bool(
        float(hard_alignment["mean_score_label_spearman"]) > 0.50
        and float(hard_capture["summary"]["mean_capture_ratio"]) > 0.0
        and float(hard_capture["summary"]["min_capture_ratio"]) > 0.0
    )
    if closes:
        verdict = "Perturbation-value supervision closes the hard exact-budget learner gate on this export; independent export validation is required before any broader claim."
    elif rho_gain > 0.10:
        verdict = "Perturbation-value supervision improves hard label alignment but does not close hard exact-budget allocation capture."
    else:
        verdict = "Perturbation-value supervision does not materially improve hard label alignment or hard exact-budget allocation capture in this learner."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_perturbation_value_learner",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
        },
        "feature_dims": feature_dims,
        "target_stats": {"mean": clean_float(y_mean), "scale": clean_float(y_scale)},
        "selection": selection,
        "hard_label_alignment": hard_alignment,
        "fixed_score_hard_label_alignment": fixed_alignment,
        "hard_capture": hard_capture,
        "fixed_score_hard_capture": fixed_capture,
        "diagnosis": {
            "hard_perturbation_value_learner_closes": closes,
            "hard_mean_score_label_spearman": hard_alignment["mean_score_label_spearman"],
            "fixed_score_mean_score_label_spearman": fixed_alignment["mean_score_label_spearman"],
            "label_rho_gain": clean_float(rho_gain),
            "hard_mean_capture_ratio": hard_capture["summary"]["mean_capture_ratio"],
            "fixed_score_hard_mean_capture_ratio": fixed_capture["summary"]["mean_capture_ratio"],
            "capture_gain": clean_float(capture_gain),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "oracle_scope": "train option_error constructs forced-option perturbation labels; eval option_error is used only for diagnostic hard capture and label-alignment evaluation",
            "selection": "model selection uses calibration exact-budget deltas, not held-out hard labels",
            "budget_stress": "budgets 2, 3, and 4 are fixed before training and evaluation",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure beyond this export", "deployable policy", "independent export validation", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        **{f"budget_{int(budget)}_score": eval_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
