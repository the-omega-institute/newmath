from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_anchor_depth_compatibility_learner as compat
import _state_generation_episode_budget_transfer_audit as budget_audit
import _state_generation_hard_perturbation_value_learner as base_learner
import _state_generation_set_context_mechanism_learner as set_context


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_structured_assignment_energy.json"
DEFAULT_MD = REPORT_DIR / "state_generation_structured_assignment_energy.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_structured_assignment_energy_predictions.npz"
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


def by_budget(x: np.ndarray, n: int, depths: np.ndarray, budgets: np.ndarray) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    offset = 0
    m = len(depths)
    for budget in budgets.astype(np.int64):
        out[int(budget)] = x[offset : offset + n * m].reshape(n, m, x.shape[1]).astype(np.float32)
        offset += n * m
    return out


def score_from_feature_sum(features: np.ndarray, choice: np.ndarray) -> np.ndarray:
    return np.sum(features[np.arange(len(choice)), choice.astype(np.int64)], axis=0).astype(np.float32)


def assignment_diff_rows(
    split: dict[str, np.ndarray],
    feat_by_budget: dict[int, np.ndarray],
    depths: np.ndarray,
    competitors: dict[str, dict[int, np.ndarray]],
    *,
    max_rows: int,
    seed: int,
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    rng = np.random.default_rng(seed)
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    rows: list[np.ndarray] = []
    weights: list[float] = []
    by_competitor: dict[str, int] = {name: 0 for name in competitors}
    for budget in BUDGETS.astype(np.int64):
        for ep in np.unique(episode):
            idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
            local_error = option_error[idx]
            oracle_choice = budget_audit.exact_budget_choice_at_multiplier(episode[idx], local_error, depths, int(budget))
            oracle_rate = selected_rate(local_error, depths, oracle_choice)
            oracle_sum = score_from_feature_sum(feat_by_budget[int(budget)][idx], oracle_choice)
            for name, scores in competitors.items():
                comp_choice = budget_audit.exact_budget_choice_at_multiplier(episode[idx], scores[int(budget)][idx], depths, int(budget))
                if np.array_equal(comp_choice, oracle_choice):
                    continue
                comp_rate = selected_rate(local_error, depths, comp_choice)
                gap = comp_rate - oracle_rate
                if gap <= 0.0:
                    continue
                comp_sum = score_from_feature_sum(feat_by_budget[int(budget)][idx], comp_choice)
                rows.append((comp_sum - oracle_sum).astype(np.float32))
                weights.append(min(20.0, max(1.0, float(gap) * 100.0)))
                by_competitor[name] += 1
    if not rows:
        raise RuntimeError("no structured assignment-energy rows generated")
    x = np.stack(rows, axis=0).astype(np.float32)
    w = np.asarray(weights, dtype=np.float32)
    if len(x) > int(max_rows):
        prob = w.astype(np.float64)
        prob = prob / float(np.sum(prob))
        keep = rng.choice(np.arange(len(x)), size=int(max_rows), replace=False, p=prob)
        x = x[keep]
        w = w[keep]
    return x, w, {"assignment_rows": int(len(x)), "rows_by_competitor": by_competitor}


def selected_rate(option_error: np.ndarray, depths: np.ndarray, choice: np.ndarray) -> float:
    err = option_error[np.arange(len(choice)), choice.astype(np.int64)]
    dep = depths[choice.astype(np.int64)].astype(np.float64)
    return float(np.sum(err) / np.sum(dep))


def train_energy(x: np.ndarray, weight: np.ndarray, *, lam: float) -> np.ndarray:
    x64 = x.astype(np.float64)
    w = np.sqrt(weight.astype(np.float64)).reshape(-1, 1)
    xw = x64 * w
    y = np.ones(len(x), dtype=np.float64)
    yw = y * w.reshape(-1)
    xtx = xw.T @ xw
    xtx += float(lam) * np.eye(xtx.shape[0], dtype=np.float64)
    beta = np.linalg.solve(xtx, xw.T @ yw)
    return beta.astype(np.float64)


def predict_scores(feat_by_budget: dict[int, np.ndarray], beta: np.ndarray) -> dict[int, np.ndarray]:
    return {int(budget): (feat.astype(np.float64) @ beta.astype(np.float64)).astype(np.float64) for budget, feat in feat_by_budget.items()}


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Structured Assignment Energy",
        "",
        f"- selected lambda: `{report['diagnosis']['selected_lambda']}`",
        f"- assignment rows: `{report['training']['assignment_rows']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["structured_assignment_energy", "anchor_depth_compatibility", "scalar_mechanism", "set_context_mechanism", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a structured exact-budget assignment-energy learner")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(set_context.env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--scalar-pred", default=str(SCALAR_PRED))
    parser.add_argument("--set-context-pred", default=str(SET_CONTEXT_PRED))
    parser.add_argument("--base-pred", default=str(BASE_PRED))
    parser.add_argument("--compat-pred", default=str(REPORT_DIR / "state_generation_anchor_depth_compatibility_learner_predictions.npz"))
    parser.add_argument("--target-pred", default=str(TARGET_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=3491)
    parser.add_argument("--projection-dim", type=int, default=10)
    parser.add_argument("--max-rows", type=int, default=1200)
    parser.add_argument("--bootstrap-samples", type=int, default=80)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    depths = data["option_depths"].astype(np.int64)
    train = set_context.episode_alloc.load_split(data, "train")
    cal = set_context.episode_alloc.load_split(data, "calibration")
    eval_split = set_context.episode_alloc.load_split(data, "eval")
    hard_episodes = set_context.env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    stats = compat.fit_stats(data, latents, depths, int(args.seed), int(args.projection_dim))
    train_x = compat.build_design(data, latents, "train", train, depths, stats)
    cal_x = compat.build_design(data, latents, "calibration", cal, depths, stats)
    eval_x = compat.build_design(data, latents, "eval", eval_split, depths, stats)
    train_feat = by_budget(train_x, len(train["episode"]), depths, BUDGETS)
    cal_feat = by_budget(cal_x, len(cal["episode"]), depths, BUDGETS)
    eval_feat = by_budget(eval_x, len(eval_split["episode"]), depths, BUDGETS)
    scalar = load_scores(Path(args.scalar_pred))
    set_ctx = load_scores(Path(args.set_context_pred))
    base = load_scores(Path(args.base_pred))
    compat_scores = load_scores(Path(args.compat_pred))
    target = load_scores(Path(args.target_pred))
    row_x, row_w, row_report = assignment_diff_rows(
        train,
        train_feat,
        depths,
        competitor_score_templates(train, depths, seed=int(args.seed)),
        max_rows=int(args.max_rows),
        seed=int(args.seed) + 7,
    )
    cal_rows: list[dict[str, Any]] = []
    best_beta: np.ndarray | None = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_lam = 0.0
    for lam in (1.0, 100.0, 10000.0):
        beta = train_energy(row_x, row_w, lam=float(lam))
        cal_scores = predict_scores(cal_feat, beta)
        mean_cap, min_cap, regret = set_context.observed_capture(cal, cal_scores, np.ones(len(cal["episode"]), dtype=bool))
        rho = set_context.label_rho(cal, depths, cal_scores)
        key = (-mean_cap, -min_cap, regret)
        cal_rows.append(
            {
                "lambda": clean_float(float(lam)),
                "cal_mean_capture_ratio": mean_cap,
                "cal_min_capture_ratio": min_cap,
                "cal_mean_label_rho": rho,
                "cal_mean_regret_to_oracle": regret,
                "selection_key": [clean_float(v) for v in key],
            }
        )
        if key < best_key:
            best_key = key
            best_beta = beta
            best_lam = float(lam)
    if best_beta is None:
        raise RuntimeError("no structured assignment-energy candidate selected")

    eval_scores = predict_scores(eval_feat, best_beta)
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "structured_assignment_energy": eval_scores,
            "anchor_depth_compatibility": compat_scores,
            "scalar_mechanism": scalar,
            "set_context_mechanism": set_ctx,
            "base_perturbation_value": base,
            "mechanism_target_ceiling": target,
        }.items()
    ):
        hard_rows[name] = {
            "capture": set_context.capture_summary(eval_split, scores, hard_mask, seed=int(args.seed) + 1000 * index, samples=int(args.bootstrap_samples)),
            "label_alignment": base_learner.hard_label_alignment(eval_split, depths, BUDGETS, hard_episodes, scores),
        }

    energy_summary = hard_rows["structured_assignment_energy"]["capture"]["summary"]
    scalar_summary = hard_rows["scalar_mechanism"]["capture"]["summary"]
    compat_summary = hard_rows["anchor_depth_compatibility"]["capture"]["summary"]
    closes = bool(float(energy_summary["mean_capture_ratio"]) > 0.0 and float(energy_summary["min_capture_ratio"]) > 0.0)
    improves_scalar = bool(float(energy_summary["mean_capture_ratio"]) > float(scalar_summary["mean_capture_ratio"]))
    improves_compat = bool(float(energy_summary["mean_capture_ratio"]) > float(compat_summary["mean_capture_ratio"]))
    verdict = (
        "Structured assignment-energy learning closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "Structured assignment-energy learning improves the hard mechanism route but does not close all hard exact-budget budgets."
        if improves_scalar or improves_compat
        else "Structured assignment-energy learning does not improve held-out hard exact-budget capture over the scalar mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_structured_assignment_energy",
        "training": row_report,
        "calibration_candidates": cal_rows,
        "hard_rows": hard_rows,
        "diagnosis": {
            "structured_assignment_energy_closes": closes,
            "selected_lambda": clean_float(best_lam),
            "energy_hard_mean_capture_ratio": energy_summary["mean_capture_ratio"],
            "energy_hard_min_capture_ratio": energy_summary["min_capture_ratio"],
            "compatibility_hard_mean_capture_ratio": compat_summary["mean_capture_ratio"],
            "scalar_hard_mean_capture_ratio": scalar_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": hard_rows["mechanism_target_ceiling"]["capture"]["summary"]["mean_capture_ratio"],
            "energy_improves_scalar": improves_scalar,
            "energy_improves_compatibility": improves_compat,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "train_label_scope": "train option_error constructs exact-budget oracle assignments and assignment-level energy differences",
            "selection_scope": "calibration option_error is used only for exact-budget capture and candidate selection",
            "eval_scope": "eval option_error is used only for held-out hard capture and label-alignment measurement",
            "feature_scope": "model inputs are latent, environment, rollout-internal, episode-local set context, depth, and budget features; eval option_error is not a feature",
            "target_ceiling_scope": "mechanism target ceiling is reference-only and excluded from selection",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy beyond this export", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(Path(args.out), **{f"budget_{int(budget)}_score": eval_scores[int(budget)].astype(np.float32) for budget in BUDGETS})
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps({"status": "ok", "diagnosis": report["diagnosis"]}, ensure_ascii=False, sort_keys=True))
    return 0


def competitor_score_templates(split: dict[str, np.ndarray], depths: np.ndarray, *, seed: int) -> dict[str, dict[int, np.ndarray]]:
    rng = np.random.default_rng(seed)
    n = len(split["episode"])
    m = len(depths)
    d = depths.astype(np.float64).reshape(1, m)
    out: dict[str, dict[int, np.ndarray]] = {
        "uniform_depth": {},
        "shallow_depth": {},
        "deep_depth": {},
        "random_depth": {},
    }
    for budget in BUDGETS.astype(np.int64):
        b = float(budget)
        out["uniform_depth"][int(budget)] = np.repeat(np.abs(d - b), n, axis=0).astype(np.float64)
        out["shallow_depth"][int(budget)] = np.repeat(d, n, axis=0).astype(np.float64)
        out["deep_depth"][int(budget)] = np.repeat(-d, n, axis=0).astype(np.float64)
        noise = rng.normal(0.0, 1.0, size=(n, m))
        out["random_depth"][int(budget)] = noise.astype(np.float64)
    return out


if __name__ == "__main__":
    raise SystemExit(main())
