from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn.functional as F

import _state_generation_candidate_oracle_gap as candidate_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit
import _state_generation_hard_perturbation_value_learner as base_learner
import _state_generation_set_context_mechanism_learner as set_context


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_assignment_contrastive_mechanism.json"
DEFAULT_MD = REPORT_DIR / "state_generation_assignment_contrastive_mechanism.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_assignment_contrastive_mechanism_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
SCALAR_PRED = REPORT_DIR / "state_generation_mechanism_target_learner_predictions.npz"
SET_CONTEXT_PRED = REPORT_DIR / "state_generation_set_context_mechanism_learner_predictions.npz"
BASE_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
TARGET_PRED = REPORT_DIR / "state_generation_mechanism_aware_assignment_target_predictions.npz"
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


def standardize_design(train_x: np.ndarray, *others: np.ndarray) -> tuple[np.ndarray, list[np.ndarray], np.ndarray, np.ndarray]:
    mean = np.mean(train_x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(train_x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    train_z = ((train_x.astype(np.float32) - mean) / scale).astype(np.float32)
    other_z = [((x.astype(np.float32) - mean) / scale).astype(np.float32) for x in others]
    return train_z, other_z, mean, scale


def by_budget(x: np.ndarray, n: int, depths: np.ndarray, budgets: np.ndarray) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    offset = 0
    m = len(depths)
    for budget in budgets.astype(np.int64):
        out[int(budget)] = x[offset : offset + n * m].reshape(n, m, x.shape[1]).astype(np.float32)
        offset += n * m
    return out


def build_features(
    data: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
    split_name: str,
    split: dict[str, np.ndarray],
    depths: np.ndarray,
    stats: dict[str, np.ndarray],
) -> np.ndarray:
    features = set_context.build_option_features(
        data,
        latents,
        split_name,
        split,
        depths,
        x_mean=stats["x_mean"],
        x_scale=stats["x_scale"],
        x_proj=stats["x_proj"],
        env_mean=stats["env_mean"],
        env_scale=stats["env_scale"],
        mech_mean=stats["mech_mean"],
        mech_scale=stats["mech_scale"],
    )
    return set_context.design_matrix(features, depths, BUDGETS).astype(np.float32)


def fit_feature_stats(
    data: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
    seed: int,
    projection_dim: int,
) -> dict[str, np.ndarray]:
    train = episode_alloc.load_split(data, "train")
    depths = data["option_depths"].astype(np.int64)
    x_mean, x_scale = set_context.standardizer(data["train_x"].astype(np.float32))
    x_proj = set_context.random_projector(data["train_x"].shape[1], int(projection_dim), int(seed))
    train_env = set_context.geometry_alloc.env_feature_matrix(data, latents, "train")
    env_mean, env_scale = set_context.standardizer(train_env)
    train_mech = set_context.mech_value.rollout_option_features(data, "train", depths)
    mech_mean, mech_scale = set_context.standardizer(train_mech.reshape(-1, train_mech.shape[2]))
    _ = train
    return {
        "x_mean": x_mean,
        "x_scale": x_scale,
        "x_proj": x_proj,
        "env_mean": env_mean,
        "env_scale": env_scale,
        "mech_mean": mech_mean,
        "mech_scale": mech_scale,
    }


def balanced_pair_rows(
    split: dict[str, np.ndarray],
    feat: dict[int, np.ndarray],
    depths: np.ndarray,
    *,
    max_rows: int,
    seed: int,
    min_gap: float,
    pair_samples_per_episode: int,
    alt_samples_per_pair: int,
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    rng = np.random.default_rng(seed)
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    pairs: list[np.ndarray] = []
    weights: list[float] = []
    per_budget: dict[str, int] = {}
    depth_to_pairs: dict[int, list[tuple[int, int]]] = {}
    for a, da in enumerate(depths.astype(np.int64)):
        for b, db in enumerate(depths.astype(np.int64)):
            depth_to_pairs.setdefault(int(da + db), []).append((a, b))
    for budget in BUDGETS.astype(np.int64):
        count_before = len(pairs)
        for ep in np.unique(episode):
            idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
            oracle_choice = budget_audit.exact_budget_choice_at_multiplier(episode[idx], option_error[idx], depths, int(budget))
            if len(idx) < 2:
                continue
            seen: set[tuple[int, int]] = set()
            attempts = max(int(pair_samples_per_episode) * 3, int(pair_samples_per_episode))
            for _ in range(attempts):
                if len(seen) >= int(pair_samples_per_episode):
                    break
                left_pos, right_pos = rng.choice(len(idx), size=2, replace=False)
                left_pos = int(left_pos)
                right_pos = int(right_pos)
                if left_pos > right_pos:
                    left_pos, right_pos = right_pos, left_pos
                pair_key = (left_pos, right_pos)
                if pair_key in seen:
                    continue
                seen.add(pair_key)
                left = int(idx[left_pos])
                right = int(idx[right_pos])
                left_choice = int(oracle_choice[left_pos])
                right_choice = int(oracle_choice[right_pos])
                depth_sum = int(depths[left_choice] + depths[right_choice])
                oracle_err = float(option_error[left, left_choice] + option_error[right, right_choice])
                oracle_feat = feat[int(budget)][left, left_choice] + feat[int(budget)][right, right_choice]
                alternatives = [
                    (alt_left, alt_right)
                    for alt_left, alt_right in depth_to_pairs.get(depth_sum, [])
                    if not (alt_left == left_choice and alt_right == right_choice)
                ]
                if len(alternatives) > int(alt_samples_per_pair):
                    take = rng.choice(np.arange(len(alternatives)), size=int(alt_samples_per_pair), replace=False)
                    alternatives = [alternatives[int(i)] for i in take]
                for alt_left, alt_right in alternatives:
                    alt_err = float(option_error[left, alt_left] + option_error[right, alt_right])
                    gap = alt_err - oracle_err
                    if gap <= float(min_gap):
                        continue
                    alt_feat = feat[int(budget)][left, alt_left] + feat[int(budget)][right, alt_right]
                    pairs.append((alt_feat - oracle_feat).astype(np.float32))
                    weights.append(min(10.0, max(1.0, gap / max(float(min_gap), 1.0e-6))))
        per_budget[f"budget_{int(budget)}"] = int(len(pairs) - count_before)
    if not pairs:
        raise RuntimeError("no assignment-contrastive pair rows generated")
    x = np.stack(pairs, axis=0).astype(np.float32)
    w = np.asarray(weights, dtype=np.float32)
    if len(x) > int(max_rows):
        prob = w.astype(np.float64)
        prob = prob / float(np.sum(prob))
        keep = rng.choice(np.arange(len(x)), size=int(max_rows), replace=False, p=prob)
        x = x[keep]
        w = w[keep]
    return x, w, {"pair_rows": int(len(x)), "rows_by_budget": per_budget}


def train_linear_contrastive(
    x: np.ndarray,
    weight: np.ndarray,
    *,
    seed: int,
    epochs: int,
    lr: float,
    l2: float,
) -> np.ndarray:
    torch.manual_seed(int(seed))
    beta = torch.zeros(x.shape[1], dtype=torch.float32, requires_grad=True)
    x_t = torch.from_numpy(x.astype(np.float32))
    w_t = torch.from_numpy(weight.astype(np.float32))
    opt = torch.optim.AdamW([beta], lr=float(lr), weight_decay=0.0)
    for _epoch in range(int(epochs)):
        margin = x_t @ beta
        loss = torch.mean(F.softplus(-margin) * w_t) + float(l2) * torch.mean(beta * beta)
        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()
    return beta.detach().cpu().numpy().astype(np.float64)


def predict_scores(x_by_budget: dict[int, np.ndarray], beta: np.ndarray) -> dict[int, np.ndarray]:
    return {int(budget): (x.astype(np.float64) @ beta.astype(np.float64)).astype(np.float64) for budget, x in x_by_budget.items()}


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


def observed_capture(split: dict[str, np.ndarray], scores: dict[int, np.ndarray]) -> tuple[float, float, float]:
    summary = capture_summary(split, scores, np.ones(len(split["episode"]), dtype=bool), seed=17, samples=50)["summary"]
    return (
        float(summary["mean_capture_ratio"]),
        float(summary["min_capture_ratio"]),
        float(summary["mean_regret_to_oracle"]),
    )


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Assignment-Contrastive Mechanism",
        "",
        f"- selected lambda: `{report['diagnosis']['selected_l2']}`",
        f"- train pair rows: `{report['training']['pair_rows']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["assignment_contrastive", "scalar_mechanism", "set_context_mechanism", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an exact-budget pair-swap contrastive assignment mechanism")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--scalar-pred", default=str(SCALAR_PRED))
    parser.add_argument("--set-context-pred", default=str(SET_CONTEXT_PRED))
    parser.add_argument("--base-pred", default=str(BASE_PRED))
    parser.add_argument("--target-pred", default=str(TARGET_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2879)
    parser.add_argument("--projection-dim", type=int, default=24)
    parser.add_argument("--max-pairs", type=int, default=1200)
    parser.add_argument("--pair-samples-per-episode", type=int, default=8)
    parser.add_argument("--alt-samples-per-pair", type=int, default=3)
    parser.add_argument("--epochs", type=int, default=20)
    parser.add_argument("--lr", type=float, default=2.0e-2)
    parser.add_argument("--min-gap", type=float, default=1.0e-5)
    parser.add_argument("--bootstrap-samples", type=int, default=30)
    args = parser.parse_args()
    start_time = time.time()

    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    depths = data["option_depths"].astype(np.int64)
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))

    stats = fit_feature_stats(data, latents, int(args.seed), int(args.projection_dim))
    train_x = build_features(data, latents, "train", train, depths, stats)
    cal_x = build_features(data, latents, "calibration", cal, depths, stats)
    eval_x = build_features(data, latents, "eval", eval_split, depths, stats)
    train_z, (cal_z, eval_z), x_mean, x_scale = standardize_design(train_x, cal_x, eval_x)
    train_by_budget = by_budget(train_z, len(train["episode"]), depths, BUDGETS)
    cal_by_budget = by_budget(cal_z, len(cal["episode"]), depths, BUDGETS)
    eval_by_budget = by_budget(eval_z, len(eval_split["episode"]), depths, BUDGETS)

    pair_x, pair_w, pair_report = balanced_pair_rows(
        train,
        train_by_budget,
        depths,
        max_rows=int(args.max_pairs),
        seed=int(args.seed) + 13,
        min_gap=float(args.min_gap),
        pair_samples_per_episode=int(args.pair_samples_per_episode),
        alt_samples_per_pair=int(args.alt_samples_per_pair),
    )
    candidates: list[dict[str, Any]] = []
    best_beta: np.ndarray | None = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_l2 = 0.0
    for l2 in (1.0e-5, 1.0e-4, 1.0e-3, 1.0e-2):
        beta = train_linear_contrastive(pair_x, pair_w, seed=int(args.seed), epochs=int(args.epochs), lr=float(args.lr), l2=float(l2))
        cal_scores = predict_scores(cal_by_budget, beta)
        mean_cap, min_cap, regret = observed_capture(cal, cal_scores)
        rho = set_context.label_rho(cal, depths, cal_scores)
        key = (-mean_cap, -min_cap, regret)
        candidates.append(
            {
                "l2": clean_float(float(l2)),
                "cal_mean_capture_ratio": clean_float(mean_cap),
                "cal_min_capture_ratio": clean_float(min_cap),
                "cal_mean_regret_to_oracle": clean_float(regret),
                "cal_mean_label_rho": clean_float(rho),
                "selection_key": [clean_float(v) for v in key],
            }
        )
        if key < best_key:
            best_key = key
            best_beta = beta
            best_l2 = float(l2)
    if best_beta is None:
        raise RuntimeError("no contrastive candidate selected")

    eval_scores = predict_scores(eval_by_budget, best_beta)
    scalar = load_scores(Path(args.scalar_pred))
    set_ctx = load_scores(Path(args.set_context_pred))
    base = load_scores(Path(args.base_pred))
    target = load_scores(Path(args.target_pred))
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "assignment_contrastive": eval_scores,
            "scalar_mechanism": scalar,
            "set_context_mechanism": set_ctx,
            "base_perturbation_value": base,
            "mechanism_target_ceiling": target,
        }.items()
    ):
        hard_rows[name] = {
            "capture": capture_summary(eval_split, scores, hard_mask, seed=int(args.seed) + 2000 + 1000 * index, samples=int(args.bootstrap_samples)),
            "label_alignment": base_learner.hard_label_alignment(eval_split, depths, BUDGETS, hard_episodes, scores),
        }

    con_summary = hard_rows["assignment_contrastive"]["capture"]["summary"]
    scalar_summary = hard_rows["scalar_mechanism"]["capture"]["summary"]
    base_summary = hard_rows["base_perturbation_value"]["capture"]["summary"]
    closes = bool(float(con_summary["mean_capture_ratio"]) > 0.0 and float(con_summary["min_capture_ratio"]) > 0.0)
    improves_scalar = bool(float(con_summary["mean_capture_ratio"]) > float(scalar_summary["mean_capture_ratio"]))
    improves_base = bool(float(con_summary["mean_capture_ratio"]) > float(base_summary["mean_capture_ratio"]))
    verdict = (
        "Assignment-contrastive mechanism learning closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "Assignment-contrastive mechanism learning improves the hard mechanism route but does not close all hard exact-budget budgets."
        if improves_scalar or improves_base
        else "Assignment-contrastive mechanism learning does not improve held-out hard exact-budget capture over the scalar mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_assignment_contrastive_mechanism",
        "config": {
            "seed": int(args.seed),
            "projection_dim": int(args.projection_dim),
            "max_pairs": int(args.max_pairs),
            "pair_samples_per_episode": int(args.pair_samples_per_episode),
            "alt_samples_per_pair": int(args.alt_samples_per_pair),
            "epochs": int(args.epochs),
            "lr": clean_float(float(args.lr)),
            "min_gap": clean_float(float(args.min_gap)),
            "bootstrap_samples": int(args.bootstrap_samples),
        },
        "training": {
            **pair_report,
            "feature_dim": int(train_z.shape[1]),
            "design_standardizer_mean_l2": clean_float(float(np.linalg.norm(x_mean.astype(np.float64)))),
            "design_standardizer_scale_mean": clean_float(float(np.mean(x_scale.astype(np.float64)))),
        },
        "calibration_candidates": candidates,
        "hard_rows": hard_rows,
        "diagnosis": {
            "assignment_contrastive_closes": closes,
            "selected_l2": clean_float(best_l2),
            "contrastive_hard_mean_capture_ratio": con_summary["mean_capture_ratio"],
            "contrastive_hard_min_capture_ratio": con_summary["min_capture_ratio"],
            "scalar_hard_mean_capture_ratio": scalar_summary["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": hard_rows["mechanism_target_ceiling"]["capture"]["summary"]["mean_capture_ratio"],
            "contrastive_improves_scalar": improves_scalar,
            "contrastive_improves_base": improves_base,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "train_label_scope": "train option_error constructs exact-budget oracle assignments and balanced pair-swap contrastive rows",
            "selection_scope": "calibration option_error is used only for exact-budget capture and candidate selection",
            "eval_scope": "eval option_error is used only for held-out hard capture and label-alignment measurement",
            "feature_scope": "model inputs are latent, environment, rollout-internal, episode-local set context, depth, and budget features; eval option_error is not a feature",
            "target_ceiling_scope": "mechanism target ceiling is reference-only and excluded from selection",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy beyond this export", "independent export validation", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(Path(args.out), **{f"budget_{int(budget)}_score": eval_scores[int(budget)].astype(np.float32) for budget in BUDGETS})
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(
        json.dumps(
            {
                "status": report["status"],
                "schema_id": report["schema_id"],
                "diagnosis": report["diagnosis"],
                "wall_time_sec": report["wall_time_sec"],
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
