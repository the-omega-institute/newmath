from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_candidate_oracle_gap as oracle_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_hard_perturbation_value_learner as base_learner


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_assignment_bottleneck_learner.json"
DEFAULT_MD = REPORT_DIR / "state_generation_assignment_bottleneck_learner.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_assignment_bottleneck_learner_predictions.npz"
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


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0)
    scale = np.std(x.astype(np.float64), axis=0)
    scale[scale < 1.0e-6] = 1.0
    return mean.astype(np.float64), scale.astype(np.float64)


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float64) - mean.reshape(1, -1)) / scale.reshape(1, -1)).astype(np.float64)


def random_projection(dim: int, width: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    return (rng.standard_normal((dim, width)) / math.sqrt(float(width))).astype(np.float64)


def split_projected(data: dict[str, np.ndarray], split: str, mean: np.ndarray, scale: np.ndarray, proj: np.ndarray) -> np.ndarray:
    x = apply_standardizer(data[f"{split}_x"], mean, scale)
    return (x @ proj).astype(np.float64)


def option_design(proj_x: np.ndarray, depths: np.ndarray, budget: int) -> np.ndarray:
    n = proj_x.shape[0]
    rows = np.repeat(proj_x[:, None, :], len(depths), axis=1).reshape(n * len(depths), -1)
    depth_col = np.tile(((depths.astype(np.float64) - 3.0) / 2.0).reshape(1, -1), (n, 1)).reshape(-1, 1)
    budget_col = np.full((n * len(depths), 1), (float(budget) - 3.0) / 2.0, dtype=np.float64)
    return np.concatenate([rows, depth_col, budget_col], axis=1).astype(np.float64)


def flatten_targets(targets: dict[int, np.ndarray], budgets: np.ndarray) -> np.ndarray:
    return np.concatenate([targets[int(budget)].reshape(-1) for budget in budgets.astype(np.int64)], axis=0).astype(np.float64)


def design_by_budget(proj_x: np.ndarray, depths: np.ndarray, budgets: np.ndarray) -> dict[int, np.ndarray]:
    return {int(budget): option_design(proj_x, depths, int(budget)) for budget in budgets.astype(np.int64)}


def stack_design(designs: dict[int, np.ndarray], budgets: np.ndarray) -> np.ndarray:
    return np.concatenate([designs[int(budget)] for budget in budgets.astype(np.int64)], axis=0).astype(np.float64)


def fit_ridge(x: np.ndarray, y: np.ndarray, lam: float) -> dict[str, np.ndarray]:
    mean, scale = fit_standardizer(x)
    z = apply_standardizer(x, mean, scale)
    aug = np.concatenate([z, np.ones((len(z), 1), dtype=np.float64)], axis=1)
    xtx = aug.T @ aug
    xtx += float(lam) * np.eye(xtx.shape[0], dtype=np.float64)
    beta = np.linalg.solve(xtx, aug.T @ y.astype(np.float64))
    return {"beta": beta.astype(np.float64), "mean": mean, "scale": scale}


def apply_ridge(designs: dict[int, np.ndarray], model: dict[str, np.ndarray], shape: tuple[int, int]) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        z = apply_standardizer(designs[int(budget)], model["mean"], model["scale"])
        aug = np.concatenate([z, np.ones((len(z), 1), dtype=np.float64)], axis=1)
        pred = aug @ model["beta"]
        out[int(budget)] = pred.reshape(shape).astype(np.float64)
    return out


def episode_state_features(split: dict[str, np.ndarray], stage_scores: dict[int, np.ndarray], budget: int) -> np.ndarray:
    episode = split["episode"].astype(np.int64)
    scores = stage_scores[int(budget)].astype(np.float64)
    out = np.zeros((len(episode), scores.shape[1], 9), dtype=np.float64)
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        local = scores[idx].reshape(-1)
        mean = float(np.mean(local))
        std = float(np.std(local))
        if std < 1.0e-6:
            std = 1.0
        q25 = float(np.quantile(local, 0.25))
        q75 = float(np.quantile(local, 0.75))
        minimum = float(np.min(local))
        maximum = float(np.max(local))
        flat_order = np.argsort(np.argsort(local, kind="mergesort"), kind="mergesort").astype(np.float64)
        denom = max(1.0, float(len(local) - 1))
        ranks = flat_order / denom
        local_scores = scores[idx]
        out[idx, :, 0] = local_scores
        out[idx, :, 1] = (local_scores - mean) / std
        out[idx, :, 2] = ranks.reshape(len(idx), scores.shape[1])
        out[idx, :, 3] = mean
        out[idx, :, 4] = std
        out[idx, :, 5] = minimum
        out[idx, :, 6] = maximum
        out[idx, :, 7] = q25
        out[idx, :, 8] = q75
    return out.reshape(len(episode) * scores.shape[1], -1).astype(np.float64)


def nonmechanism_state_features(proj_x: np.ndarray, split: dict[str, np.ndarray], depths: np.ndarray, budget: int) -> np.ndarray:
    episode = split["episode"].astype(np.int64)
    n = len(episode)
    depth_grid = np.tile(((depths.astype(np.float64) - 3.0) / 2.0).reshape(1, -1), (n, 1))
    norm = np.linalg.norm(proj_x, axis=1)
    mean_feat = np.mean(proj_x, axis=1)
    std_feat = np.std(proj_x, axis=1)
    base = np.zeros((n, len(depths), 9), dtype=np.float64)
    for ep in np.unique(episode):
        idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
        local_norm = norm[idx]
        local_mean = mean_feat[idx]
        local_std = std_feat[idx]
        base[idx, :, 0] = norm[idx, None]
        base[idx, :, 1] = (norm[idx, None] - float(np.mean(local_norm))) / max(float(np.std(local_norm)), 1.0e-6)
        base[idx, :, 2] = depth_grid[idx]
        base[idx, :, 3] = float(np.mean(local_norm))
        base[idx, :, 4] = float(np.std(local_norm))
        base[idx, :, 5] = float(np.mean(local_mean))
        base[idx, :, 6] = float(np.std(local_mean))
        base[idx, :, 7] = float(np.mean(local_std))
        base[idx, :, 8] = (float(budget) - 3.0) / 2.0
    return base.reshape(n * len(depths), -1).astype(np.float64)


def bottleneck_design(base_design: dict[int, np.ndarray], split: dict[str, np.ndarray], stage_scores: dict[int, np.ndarray]) -> dict[int, np.ndarray]:
    return {
        int(budget): np.concatenate(
            [base_design[int(budget)], episode_state_features(split, stage_scores, int(budget))],
            axis=1,
        ).astype(np.float64)
        for budget in BUDGETS.astype(np.int64)
    }


def control_design(base_design: dict[int, np.ndarray], proj_x: np.ndarray, split: dict[str, np.ndarray], depths: np.ndarray) -> dict[int, np.ndarray]:
    return {
        int(budget): np.concatenate(
            [base_design[int(budget)], nonmechanism_state_features(proj_x, split, depths, int(budget))],
            axis=1,
        ).astype(np.float64)
        for budget in BUDGETS.astype(np.int64)
    }


def label_alignment(split: dict[str, np.ndarray], depths: np.ndarray, hard_episodes: list[int], scores: dict[int, np.ndarray]) -> dict[str, Any]:
    return base_learner.hard_label_alignment(split, depths, BUDGETS, hard_episodes, scores)


def capture_summary(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    mask: np.ndarray,
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget_index, budget in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = oracle_gap.episode_values(split, oracle_score, mask.astype(bool), int(budget))
        score_eps, score_values = oracle_gap.episode_values(split, scores[int(budget)], mask.astype(bool), int(budget))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {budget}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{int(budget)}"] = {
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


def select_model(
    train_design: dict[int, np.ndarray],
    train_targets: dict[int, np.ndarray],
    cal_design: dict[int, np.ndarray],
    cal_split: dict[str, np.ndarray],
    *,
    lambdas: tuple[float, ...],
) -> tuple[dict[str, np.ndarray], list[dict[str, Any]]]:
    train_x = stack_design(train_design, BUDGETS)
    train_y = flatten_targets(train_targets, BUDGETS)
    rows: list[dict[str, Any]] = []
    best_key = (float("inf"), float("inf"), float("inf"))
    best_model: dict[str, np.ndarray] | None = None
    template = train_targets
    cal_mask = np.ones(len(cal_split["episode"]), dtype=bool)
    for lam in lambdas:
        model = fit_ridge(train_x, train_y, float(lam))
        cal_scores = apply_ridge(cal_design, model, cal_split["option_error"].shape)
        summary = capture_summary(cal_split, cal_scores, cal_mask, seed=1701 + int(lam), samples=80)["summary"]
        key = (-float(summary["mean_capture_ratio"]), -float(summary["min_capture_ratio"]), float(summary["mean_regret_to_oracle"]))
        rows.append({"lambda": clean_float(float(lam)), "selection_key": [clean_float(v) for v in key], **summary})
        if key < best_key:
            best_key = key
            best_model = model
    if best_model is None:
        raise RuntimeError("no ridge model selected")
    return best_model, rows


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Assignment Bottleneck Learner",
        "",
        f"- bottleneck selected lambda: `{report['diagnosis']['bottleneck_selected_lambda']}`",
        f"- control selected lambda: `{report['diagnosis']['control_selected_lambda']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["assignment_bottleneck", "matched_nonmechanism_control", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Compare a non-leaky assignment-bearing bottleneck learner to a matched non-mechanism control")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=4219)
    parser.add_argument("--projection-width", type=int, default=160)
    parser.add_argument("--bootstrap-samples", type=int, default=160)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    mean, scale = fit_standardizer(data["train_x"])
    proj = random_projection(data["train_x"].shape[1], int(args.projection_width), int(args.seed))
    train_proj = split_projected(data, "train", mean, scale, proj)
    cal_proj = split_projected(data, "calibration", mean, scale, proj)
    eval_proj = split_projected(data, "eval", mean, scale, proj)
    train_base = design_by_budget(train_proj, depths, BUDGETS)
    cal_base = design_by_budget(cal_proj, depths, BUDGETS)
    eval_base = design_by_budget(eval_proj, depths, BUDGETS)
    train_targets = base_learner.forced_delta_targets(train, depths, BUDGETS)
    cal_targets = base_learner.forced_delta_targets(cal, depths, BUDGETS)

    stage_model, stage_selection = select_model(
        train_base,
        train_targets,
        cal_base,
        cal,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    train_stage = apply_ridge(train_base, stage_model, train["option_error"].shape)
    cal_stage = apply_ridge(cal_base, stage_model, cal["option_error"].shape)
    eval_stage = apply_ridge(eval_base, stage_model, eval_split["option_error"].shape)

    train_bottleneck = bottleneck_design(train_base, train, train_stage)
    cal_bottleneck = bottleneck_design(cal_base, cal, cal_stage)
    eval_bottleneck = bottleneck_design(eval_base, eval_split, eval_stage)
    train_control = control_design(train_base, train_proj, train, depths)
    cal_control = control_design(cal_base, cal_proj, cal, depths)
    eval_control = control_design(eval_base, eval_proj, eval_split, depths)
    bottleneck_model, bottleneck_selection = select_model(
        train_bottleneck,
        train_targets,
        cal_bottleneck,
        cal,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    control_model, control_selection = select_model(
        train_control,
        train_targets,
        cal_control,
        cal,
        lambdas=(1.0, 10.0, 100.0, 1000.0),
    )
    bottleneck_scores = apply_ridge(eval_bottleneck, bottleneck_model, eval_split["option_error"].shape)
    control_scores = apply_ridge(eval_control, control_model, eval_split["option_error"].shape)
    target_scores = base_learner.forced_delta_targets(eval_split, depths, BUDGETS)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "assignment_bottleneck": bottleneck_scores,
            "matched_nonmechanism_control": control_scores,
            "mechanism_target_ceiling": target_scores,
        }.items()
    ):
        hard_rows[name] = {
            "capture": capture_summary(eval_split, scores, hard_mask, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples)),
            "label_alignment": label_alignment(eval_split, depths, hard_episodes, scores),
        }

    bottleneck_summary = hard_rows["assignment_bottleneck"]["capture"]["summary"]
    control_summary = hard_rows["matched_nonmechanism_control"]["capture"]["summary"]
    target_summary = hard_rows["mechanism_target_ceiling"]["capture"]["summary"]
    bottleneck_delta = float(bottleneck_summary["mean_capture_ratio"]) - float(control_summary["mean_capture_ratio"])
    closes = bool(float(bottleneck_summary["mean_capture_ratio"]) > 0.0 and float(bottleneck_summary["min_capture_ratio"]) > 0.0)
    beats_control = bool(bottleneck_delta > 0.0)
    verdict = (
        "The assignment-bearing bottleneck learner closes the hard exact-budget gate and beats the matched non-mechanism control on this export; prediction parity and independent export validation remain required."
        if closes and beats_control
        else "The assignment-bearing bottleneck learner beats the matched non-mechanism control but does not close all hard exact-budget budgets."
        if beats_control
        else "The assignment-bearing bottleneck learner fails closed against the matched non-mechanism control on the held-out hard exact-budget gate."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_assignment_bottleneck_learner",
        "feature_dims": {
            "projection_width": int(args.projection_width),
            "base_design": int(next(iter(train_base.values())).shape[1]),
            "bottleneck_design": int(next(iter(train_bottleneck.values())).shape[1]),
            "control_design": int(next(iter(train_control.values())).shape[1]),
        },
        "selection": {
            "stage": stage_selection,
            "assignment_bottleneck": bottleneck_selection,
            "matched_nonmechanism_control": control_selection,
        },
        "hard_rows": hard_rows,
        "diagnosis": {
            "assignment_bottleneck_closes": closes,
            "assignment_bottleneck_beats_control": beats_control,
            "bottleneck_minus_control_mean_capture": clean_float(bottleneck_delta),
            "bottleneck_hard_mean_capture_ratio": bottleneck_summary["mean_capture_ratio"],
            "control_hard_mean_capture_ratio": control_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": target_summary["mean_capture_ratio"],
            "bottleneck_selected_lambda": bottleneck_selection[0]["lambda"],
            "control_selected_lambda": control_selection[0]["lambda"],
            "stage_selected_lambda": stage_selection[0]["lambda"],
            "prediction_parity_checked": False,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "both arms use only train-standardized current/past latent-action and rollout-internal features from aligned_state_generation_export; eval option_error is not a feature",
            "labels": "train option_error constructs forced-delta mechanism labels for supervised training; calibration option_error is used only for model selection",
            "final_eval": "held-out hard eval episodes are used only after model and lambda selection",
            "matched_control": "the non-mechanism control shares the same projected inputs, target labels, ridge family, lambdas, and calibration rule but omits the learned assignment-state bottleneck summaries",
        },
        "not_claimed": [
            "prediction parity",
            "deployable policy beyond this export",
            "independent export validation",
            "complete BEDC-native world model",
        ],
    }
    np.savez_compressed(
        Path(args.out),
        **{f"budget_{int(budget)}_score": bottleneck_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
        **{f"control_budget_{int(budget)}_score": control_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"status": "ok", "diagnosis": report["diagnosis"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
