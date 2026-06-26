from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_budget_conditioned_value as budget_value
import _state_generation_candidate_oracle_gap as candidate_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_geometry_option_conditioned_allocation as option_alloc
import _state_generation_hard_perturbation_value as hard_value
import _state_generation_hard_perturbation_value_learner as base_learner
import _state_generation_mechanism_conditioned_value as mech_value


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_set_context_mechanism_learner.json"
DEFAULT_MD = REPORT_DIR / "state_generation_set_context_mechanism_learner.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_set_context_mechanism_learner_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
MECHANISM_LEARNER_PRED = REPORT_DIR / "state_generation_mechanism_target_learner_predictions.npz"
BASE_LEARNER_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
TARGET_CEILING_PRED = REPORT_DIR / "state_generation_mechanism_aware_assignment_target_predictions.npz"
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


def standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def rank_vector(v: np.ndarray) -> np.ndarray:
    order = np.argsort(v.astype(np.float64), kind="mergesort")
    ranks = np.zeros(len(v), dtype=np.float64)
    ranks[order] = np.arange(len(v), dtype=np.float64)
    denom = max(1, len(v) - 1)
    return (ranks / float(denom)).astype(np.float32)


def episode_context(values: np.ndarray, episode: np.ndarray) -> np.ndarray:
    n, m, d = values.shape
    out = np.zeros((n, m, d * 3), dtype=np.float32)
    for ep in np.unique(episode.astype(np.int64)):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        local = values[idx].astype(np.float64)
        mean = np.mean(local.reshape(-1, d), axis=0)
        scale = np.std(local.reshape(-1, d), axis=0)
        scale[scale < 1.0e-6] = 1.0
        z = ((local - mean.reshape(1, 1, d)) / scale.reshape(1, 1, d)).astype(np.float32)
        ranks = np.zeros_like(z, dtype=np.float32)
        for col in range(d):
            ranks[:, :, col] = rank_vector(local[:, :, col].reshape(-1)).reshape(len(idx), m)
        out[idx] = np.concatenate([values[idx].astype(np.float32), z, ranks], axis=2)
    return out.astype(np.float32)


def random_projector(dim: int, out_dim: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    mat = rng.normal(0.0, 1.0 / math.sqrt(float(out_dim)), size=(dim, out_dim)).astype(np.float32)
    return mat


def compact_anchor_features(data: dict[str, np.ndarray], split: str, mean: np.ndarray, scale: np.ndarray, proj: np.ndarray) -> np.ndarray:
    x = apply_standardizer(data[f"{split}_x"].astype(np.float32), mean, scale)
    return (x @ proj).astype(np.float32)


def build_option_features(
    data: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
    split_name: str,
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    *,
    x_mean: np.ndarray,
    x_scale: np.ndarray,
    x_proj: np.ndarray,
    env_mean: np.ndarray,
    env_scale: np.ndarray,
    mech_mean: np.ndarray,
    mech_scale: np.ndarray,
) -> np.ndarray:
    n = len(split["episode"])
    m = len(depths)
    anchor = compact_anchor_features(data, split_name, x_mean, x_scale, x_proj)
    env = geometry_alloc.env_feature_matrix(data, latents, split_name)
    env_z = apply_standardizer(env, env_mean, env_scale)
    mech = mech_value.rollout_option_features(data, split_name, depths)
    mech_z = apply_standardizer(mech.reshape(-1, mech.shape[2]), mech_mean, mech_scale).reshape(mech.shape)
    mech_ctx = episode_context(mech_z, split["episode"].astype(np.int64))
    opt = option_alloc.option_features(depths).astype(np.float32)
    anchor_rep = np.repeat(anchor[:, None, :], m, axis=1)
    env_rep = np.repeat(env_z[:, None, :], m, axis=1)
    opt_rep = np.repeat(opt[None, :, :], n, axis=0)
    depth = np.repeat(depths.astype(np.float32).reshape(1, m, 1), n, axis=0)
    episode_len = np.zeros((n, 1), dtype=np.float32)
    for ep in np.unique(split["episode"].astype(np.int64)):
        idx = np.flatnonzero(split["episode"] == int(ep)).astype(np.int64)
        episode_len[idx, 0] = float(len(idx))
    episode_len = np.repeat(episode_len[:, None, :], m, axis=1)
    return np.concatenate([anchor_rep, env_rep, opt_rep, mech_z, mech_ctx, depth / 5.0, episode_len / 128.0], axis=2).astype(np.float32)


def budget_features(budget: int, depths: np.ndarray, option_features: np.ndarray) -> np.ndarray:
    n, m, _d = option_features.shape
    b = float(budget)
    depth = depths.astype(np.float32).reshape(1, m, 1)
    budget_token = np.asarray([b - 3.0, (b - 3.0) * (b - 3.0), float(b == 2), float(b == 3), float(b == 4)], dtype=np.float32)
    budget_rep = np.repeat(budget_token.reshape(1, 1, -1), n * m, axis=0).reshape(n, m, -1)
    pressure = np.concatenate(
        [
            depth / b,
            np.abs(depth - b) / b,
            (depth < b).astype(np.float32),
            (depth == b).astype(np.float32),
            (depth > b).astype(np.float32),
        ],
        axis=2,
    )
    pressure = np.repeat(pressure, n, axis=0).reshape(n, m, -1)
    return np.concatenate([option_features, budget_rep, pressure], axis=2).reshape(n * m, -1).astype(np.float32)


def flatten_targets(targets: dict[int, np.ndarray], budgets: np.ndarray) -> np.ndarray:
    return np.concatenate([targets[int(budget)].reshape(-1) for budget in budgets.astype(np.int64)], axis=0).astype(np.float64)


def design_matrix(option_features: np.ndarray, depths: np.ndarray, budgets: np.ndarray) -> np.ndarray:
    return np.concatenate([budget_features(int(budget), depths, option_features) for budget in budgets.astype(np.int64)], axis=0).astype(np.float32)


def weighted_ridge(x: np.ndarray, y: np.ndarray, weight: np.ndarray, lam: float) -> tuple[np.ndarray, float]:
    x64 = x.astype(np.float64)
    y64 = y.astype(np.float64)
    w = np.sqrt(weight.astype(np.float64)).reshape(-1, 1)
    xw = x64 * w
    yw = y64 * w.reshape(-1)
    xtx = xw.T @ xw
    xtx += float(lam) * np.eye(xtx.shape[0], dtype=np.float64)
    beta = np.linalg.solve(xtx, xw.T @ yw)
    return beta.astype(np.float64), 0.0


def predict_scores(x: np.ndarray, beta: np.ndarray, n: int, depths: np.ndarray, budgets: np.ndarray) -> dict[int, np.ndarray]:
    pred = (x.astype(np.float64) @ beta.astype(np.float64)).astype(np.float64)
    out: dict[int, np.ndarray] = {}
    offset = 0
    m = len(depths)
    for budget in budgets.astype(np.int64):
        out[int(budget)] = pred[offset : offset + n * m].reshape(n, m).astype(np.float64)
        offset += n * m
    return out


def label_rho(split: dict[str, np.ndarray], depths: np.ndarray, scores: dict[int, np.ndarray]) -> float:
    labels = base_learner.forced_delta_targets(split, depths, BUDGETS)
    rhos = [hard_value.spearman(scores[int(budget)].reshape(-1), labels[int(budget)].reshape(-1)) for budget in BUDGETS.astype(np.int64)]
    return clean_float(float(np.mean(rhos)))


def observed_capture(split: dict[str, np.ndarray], scores: dict[int, np.ndarray], mask: np.ndarray) -> tuple[float, float, float]:
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget in BUDGETS.astype(np.int64):
        oracle_eps, oracle_values = candidate_gap.episode_values(split, oracle_score, mask.astype(bool), int(budget))
        score_eps, score_values = candidate_gap.episode_values(split, scores[int(budget)], mask.astype(bool), int(budget))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {budget}")
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        captures.append(float(score_mean / oracle_mean) if oracle_mean < 0.0 else 0.0)
        regrets.append(float(np.mean(score_values - oracle_values)))
    return clean_float(float(np.mean(captures))), clean_float(float(np.min(captures))), clean_float(float(np.mean(regrets)))


def capture_summary(split: dict[str, np.ndarray], scores: dict[int, np.ndarray], mask: np.ndarray, *, seed: int, samples: int) -> dict[str, Any]:
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget_index, budget in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = candidate_gap.episode_values(split, oracle_score, mask.astype(bool), int(budget))
        score_eps, score_values = candidate_gap.episode_values(split, scores[int(budget)], mask.astype(bool), int(budget))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {budget}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{int(budget)}"] = {
            "score_delta": candidate_gap.bootstrap_mean(score_values, seed=seed + 1009 * budget_index, samples=samples),
            "oracle_delta": candidate_gap.bootstrap_mean(oracle_values, seed=seed + 1009 * budget_index + 17, samples=samples),
            "regret_to_oracle": candidate_gap.bootstrap_mean(regret, seed=seed + 1009 * budget_index + 31, samples=samples),
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


def tail_weights(targets: np.ndarray, tail_weight: float) -> np.ndarray:
    threshold = float(np.quantile(targets.astype(np.float64), 0.90))
    return (1.0 + float(tail_weight) * (targets >= threshold).astype(np.float64)).astype(np.float64)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Set-Context Mechanism Learner",
        "",
        f"- selected lambda: `{report['diagnosis']['selected_lambda']}`",
        f"- selected tail weight: `{report['diagnosis']['selected_tail_weight']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["set_context_mechanism", "mechanism_scalar_learner", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a set-context ridge learner for mechanism targets")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--mechanism-pred", default=str(MECHANISM_LEARNER_PRED))
    parser.add_argument("--base-pred", default=str(BASE_LEARNER_PRED))
    parser.add_argument("--target-pred", default=str(TARGET_CEILING_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2531)
    parser.add_argument("--projection-dim", type=int, default=24)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    depths = data["option_depths"].astype(np.int64)
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))

    x_mean, x_scale = standardizer(data["train_x"].astype(np.float32))
    x_proj = random_projector(data["train_x"].shape[1], int(args.projection_dim), int(args.seed))
    train_env = geometry_alloc.env_feature_matrix(data, latents, "train")
    env_mean, env_scale = standardizer(train_env)
    train_mech = mech_value.rollout_option_features(data, "train", depths)
    mech_mean, mech_scale = standardizer(train_mech.reshape(-1, train_mech.shape[2]))

    train_feat = build_option_features(data, latents, "train", train, depths, x_mean=x_mean, x_scale=x_scale, x_proj=x_proj, env_mean=env_mean, env_scale=env_scale, mech_mean=mech_mean, mech_scale=mech_scale)
    cal_feat = build_option_features(data, latents, "calibration", cal, depths, x_mean=x_mean, x_scale=x_scale, x_proj=x_proj, env_mean=env_mean, env_scale=env_scale, mech_mean=mech_mean, mech_scale=mech_scale)
    eval_feat = build_option_features(data, latents, "eval", eval_split, depths, x_mean=x_mean, x_scale=x_scale, x_proj=x_proj, env_mean=env_mean, env_scale=env_scale, mech_mean=mech_mean, mech_scale=mech_scale)
    train_x = design_matrix(train_feat, depths, BUDGETS)
    cal_x = design_matrix(cal_feat, depths, BUDGETS)
    eval_x = design_matrix(eval_feat, depths, BUDGETS)
    train_targets = base_learner.forced_delta_targets(train, depths, BUDGETS)
    train_y = flatten_targets(train_targets, BUDGETS)
    cal_rows: list[dict[str, Any]] = []
    best_key = (float("inf"), float("inf"), float("inf"))
    best_beta: np.ndarray | None = None
    best_cfg: dict[str, float] = {}
    for lam in (1.0, 100.0, 10000.0):
        for tw in (0.0, 2.0):
            weights = tail_weights(train_y, tw)
            beta, _ = weighted_ridge(train_x, train_y, weights, lam)
            cal_scores = predict_scores(cal_x, beta, len(cal["episode"]), depths, BUDGETS)
            mean_cap, min_cap, regret = observed_capture(cal, cal_scores, np.ones(len(cal["episode"]), dtype=bool))
            rho = label_rho(cal, depths, cal_scores)
            key = (-mean_cap, -min_cap, -rho, regret)
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
        raise RuntimeError("no ridge candidate selected")
    eval_scores = predict_scores(eval_x, best_beta, len(eval_split["episode"]), depths, BUDGETS)
    scalar_scores = load_scores(Path(args.mechanism_pred))
    base_scores = load_scores(Path(args.base_pred))
    target_scores = load_scores(Path(args.target_pred))
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "set_context_mechanism": eval_scores,
            "mechanism_scalar_learner": scalar_scores,
            "base_perturbation_value": base_scores,
            "mechanism_target_ceiling": target_scores,
        }.items()
    ):
        hard_rows[name] = {
            "capture": capture_summary(eval_split, scores, hard_mask, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples)),
            "label_alignment": base_learner.hard_label_alignment(eval_split, depths, BUDGETS, hard_episodes, scores),
        }
    set_summary = hard_rows["set_context_mechanism"]["capture"]["summary"]
    scalar_summary = hard_rows["mechanism_scalar_learner"]["capture"]["summary"]
    base_summary = hard_rows["base_perturbation_value"]["capture"]["summary"]
    target_summary = hard_rows["mechanism_target_ceiling"]["capture"]["summary"]
    closes = bool(float(set_summary["mean_capture_ratio"]) > 0.0 and float(set_summary["min_capture_ratio"]) > 0.0)
    improves_scalar = bool(float(set_summary["mean_capture_ratio"]) > float(scalar_summary["mean_capture_ratio"]))
    improves_base = bool(float(set_summary["mean_capture_ratio"]) > float(base_summary["mean_capture_ratio"]))
    verdict = (
        "Set-context mechanism learning closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "Set-context mechanism learning improves the hard mechanism route but does not close all hard exact-budget budgets."
        if improves_scalar or improves_base
        else "Set-context mechanism learning does not improve held-out hard exact-budget capture over the scalar mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_set_context_mechanism_learner",
        "feature_dim": int(train_x.shape[1]),
        "train_rows": int(train_x.shape[0]),
        "calibration_candidates": cal_rows,
        "hard_rows": hard_rows,
        "diagnosis": {
            "set_context_mechanism_closes": closes,
            "selected_lambda": best_cfg["lambda"],
            "selected_tail_weight": best_cfg["tail_weight"],
            "set_context_hard_mean_capture_ratio": set_summary["mean_capture_ratio"],
            "set_context_hard_min_capture_ratio": set_summary["min_capture_ratio"],
            "scalar_hard_mean_capture_ratio": scalar_summary["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": target_summary["mean_capture_ratio"],
            "set_context_improves_scalar": improves_scalar,
            "set_context_improves_base": improves_base,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "train_label_scope": "train option_error constructs forced-delta mechanism labels for supervised ridge training",
            "selection_scope": "calibration option_error constructs forced-delta labels and exact-budget capture only for model selection",
            "eval_scope": "eval option_error is used only for held-out hard capture and label-alignment measurement",
            "feature_scope": "model inputs are random-projected latent state, environment, rollout-internal, episode-local set context, option-depth, and budget features",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy beyond this export", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(Path(args.out), **{f"budget_{int(budget)}_score": eval_scores[int(budget)].astype(np.float32) for budget in BUDGETS})
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
