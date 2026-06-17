from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_candidate_oracle_gap as candidate_gap
import _state_generation_hard_perturbation_value_learner as base_learner
import _state_generation_set_context_mechanism_learner as set_context


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_assignment_state_encoder.json"
DEFAULT_MD = REPORT_DIR / "state_generation_assignment_state_encoder.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_assignment_state_encoder_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
SCALAR_PRED = REPORT_DIR / "state_generation_mechanism_target_learner_predictions.npz"
SET_CONTEXT_PRED = REPORT_DIR / "state_generation_set_context_mechanism_learner_predictions.npz"
BASE_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
COMPAT_PRED = REPORT_DIR / "state_generation_anchor_depth_compatibility_learner_predictions.npz"
ENERGY_PRED = REPORT_DIR / "state_generation_structured_assignment_energy_predictions.npz"
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


def episode_state_matrix(split: dict[str, np.ndarray], scores: dict[str, dict[int, np.ndarray]]) -> dict[int, np.ndarray]:
    episode = split["episode"].astype(np.int64)
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        rows = np.zeros((len(episode), len(scores) * 6 + 2), dtype=np.float64)
        for ep in np.unique(episode):
            idx = np.flatnonzero(episode == int(ep)).astype(np.int64)
            feats: list[float] = []
            for name in sorted(scores):
                local = scores[name][int(budget)][idx].astype(np.float64)
                feats.extend(
                    [
                        float(np.mean(local)),
                        float(np.std(local)),
                        float(np.min(local)),
                        float(np.max(local)),
                        float(np.quantile(local, 0.25)),
                        float(np.quantile(local, 0.75)),
                    ]
                )
            feats.extend([float(len(idx)) / 128.0, float(budget - 3)])
            rows[idx] = np.asarray(feats, dtype=np.float64)
        out[int(budget)] = rows.astype(np.float64)
    return out


def build_design(split: dict[str, np.ndarray], base_scores: dict[str, dict[int, np.ndarray]], state: dict[int, np.ndarray]) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        mats = [base_scores[name][int(budget)].reshape(-1, 1) for name in sorted(base_scores)]
        n, m = base_scores[sorted(base_scores)[0]][int(budget)].shape
        state_rep = np.repeat(state[int(budget)][:, None, :], m, axis=1).reshape(n * m, -1)
        depth_rank = np.tile(np.linspace(0.0, 1.0, m, dtype=np.float64).reshape(1, m, 1), (n, 1, 1)).reshape(n * m, 1)
        out[int(budget)] = np.concatenate([*(mat.reshape(n * m, 1) for mat in mats), state_rep, depth_rank], axis=1).astype(np.float64)
    return out


def flatten_scores(scores: dict[int, np.ndarray]) -> np.ndarray:
    return np.concatenate([scores[int(budget)].reshape(-1) for budget in BUDGETS.astype(np.int64)], axis=0)


def predict(design: dict[int, np.ndarray], beta: np.ndarray, template: dict[int, np.ndarray]) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for budget in BUDGETS.astype(np.int64):
        pred = design[int(budget)] @ beta.astype(np.float64)
        out[int(budget)] = pred.reshape(template[int(budget)].shape).astype(np.float64)
    return out


def fit_ridge(x: np.ndarray, y: np.ndarray, lam: float) -> np.ndarray:
    mean = np.mean(x, axis=0)
    scale = np.std(x, axis=0)
    scale[scale < 1.0e-6] = 1.0
    z = (x - mean.reshape(1, -1)) / scale.reshape(1, -1)
    aug = np.concatenate([z, np.ones((len(z), 1), dtype=np.float64)], axis=1)
    xtx = aug.T @ aug
    xtx += float(lam) * np.eye(xtx.shape[0], dtype=np.float64)
    beta = np.linalg.solve(xtx, aug.T @ y.astype(np.float64))
    packed = np.concatenate([beta, mean, scale], axis=0)
    return packed.astype(np.float64)


def apply_packed(design: dict[int, np.ndarray], packed: np.ndarray, template: dict[int, np.ndarray]) -> dict[int, np.ndarray]:
    d = design[int(BUDGETS[0])].shape[1]
    beta = packed[: d + 1]
    mean = packed[d + 1 : d + 1 + d]
    scale = packed[d + 1 + d :]
    z_design = {int(budget): (design[int(budget)] - mean.reshape(1, -1)) / scale.reshape(1, -1) for budget in BUDGETS.astype(np.int64)}
    aug = {int(budget): np.concatenate([z_design[int(budget)], np.ones((z_design[int(budget)].shape[0], 1), dtype=np.float64)], axis=1) for budget in BUDGETS.astype(np.int64)}
    return predict(aug, beta, template)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Assignment-State Encoder",
        "",
        f"- selected lambda: `{report['diagnosis']['selected_lambda']}`",
        "",
        "| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["assignment_state_encoder", "anchor_depth_compatibility", "structured_assignment_energy", "scalar_mechanism", "set_context_mechanism", "base_perturbation_value", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]["capture"]["summary"]
        rho = report["hard_rows"][name]["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {row['mean_capture_ratio']:.6g} | {row['budget2_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a lightweight aggregate assignment-state adapter")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--scalar-pred", default=str(SCALAR_PRED))
    parser.add_argument("--set-context-pred", default=str(SET_CONTEXT_PRED))
    parser.add_argument("--base-pred", default=str(BASE_PRED))
    parser.add_argument("--compat-pred", default=str(COMPAT_PRED))
    parser.add_argument("--energy-pred", default=str(ENERGY_PRED))
    parser.add_argument("--target-pred", default=str(TARGET_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=3719)
    parser.add_argument("--bootstrap-samples", type=int, default=120)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    eval_split = set_context.episode_alloc.load_split(data, "eval")
    hard_episodes = set_context.env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    non_hard_mask = ~hard_mask
    scalar = load_scores(Path(args.scalar_pred))
    set_ctx = load_scores(Path(args.set_context_pred))
    base = load_scores(Path(args.base_pred))
    compat_scores = load_scores(Path(args.compat_pred))
    energy = load_scores(Path(args.energy_pred))
    target = load_scores(Path(args.target_pred))
    source_scores = {
        "anchor_depth_compatibility": compat_scores,
        "base_perturbation_value": base,
        "scalar_mechanism": scalar,
        "set_context_mechanism": set_ctx,
        "structured_assignment_energy": energy,
    }
    state = episode_state_matrix(eval_split, source_scores)
    design = build_design(eval_split, source_scores, state)
    oracle = {int(budget): eval_split["option_error"].astype(np.float64) for budget in BUDGETS}
    train_design = np.concatenate([design[int(budget)][np.repeat(non_hard_mask, oracle[int(budget)].shape[1])] for budget in BUDGETS.astype(np.int64)], axis=0)
    train_y = np.concatenate([oracle[int(budget)][non_hard_mask].reshape(-1) for budget in BUDGETS.astype(np.int64)], axis=0)
    cal_rows: list[dict[str, Any]] = []
    best_key = (float("inf"), float("inf"), float("inf"))
    best_packed: np.ndarray | None = None
    best_lam = 0.0
    for lam in (1.0, 100.0, 10000.0):
        packed = fit_ridge(train_design, train_y, float(lam))
        scores = apply_packed(design, packed, oracle)
        mean_cap, min_cap, regret = set_context.observed_capture(eval_split, scores, non_hard_mask)
        rho = set_context.label_rho(set_context.geometry_alloc.slice_eval(eval_split, non_hard_mask), data["option_depths"].astype(np.int64), {int(budget): scores[int(budget)][non_hard_mask] for budget in BUDGETS})
        key = (-mean_cap, -min_cap, regret)
        cal_rows.append(
            {
                "lambda": clean_float(float(lam)),
                "non_hard_mean_capture_ratio": mean_cap,
                "non_hard_min_capture_ratio": min_cap,
                "non_hard_mean_label_rho": rho,
                "non_hard_mean_regret_to_oracle": regret,
                "selection_key": [clean_float(v) for v in key],
            }
        )
        if key < best_key:
            best_key = key
            best_packed = packed
            best_lam = float(lam)
    if best_packed is None:
        raise RuntimeError("no aggregate assignment-state adapter selected")

    eval_scores = apply_packed(design, best_packed, oracle)
    depths = data["option_depths"].astype(np.int64)
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "assignment_state_encoder": eval_scores,
            "anchor_depth_compatibility": compat_scores,
            "structured_assignment_energy": energy,
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

    state_summary = hard_rows["assignment_state_encoder"]["capture"]["summary"]
    scalar_summary = hard_rows["scalar_mechanism"]["capture"]["summary"]
    compat_summary = hard_rows["anchor_depth_compatibility"]["capture"]["summary"]
    energy_summary = hard_rows["structured_assignment_energy"]["capture"]["summary"]
    closes = bool(float(state_summary["mean_capture_ratio"]) > 0.0 and float(state_summary["min_capture_ratio"]) > 0.0)
    improves_scalar = bool(float(state_summary["mean_capture_ratio"]) > float(scalar_summary["mean_capture_ratio"]))
    improves_compat = bool(float(state_summary["mean_capture_ratio"]) > float(compat_summary["mean_capture_ratio"]))
    improves_energy = bool(float(state_summary["mean_capture_ratio"]) > float(energy_summary["mean_capture_ratio"]))
    verdict = (
        "Aggregate assignment-state encoding closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "Aggregate assignment-state encoding improves the hard mechanism route but does not close all hard exact-budget budgets."
        if improves_scalar or improves_compat or improves_energy
        else "Aggregate assignment-state encoding does not improve held-out hard exact-budget capture over the scalar mechanism learner."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_assignment_state_encoder",
        "feature_dim": int(train_design.shape[1]),
        "selection": cal_rows,
        "hard_rows": hard_rows,
        "diagnosis": {
            "assignment_state_encoder_closes": closes,
            "selected_lambda": clean_float(best_lam),
            "state_hard_mean_capture_ratio": state_summary["mean_capture_ratio"],
            "state_hard_min_capture_ratio": state_summary["min_capture_ratio"],
            "compatibility_hard_mean_capture_ratio": compat_summary["mean_capture_ratio"],
            "energy_hard_mean_capture_ratio": energy_summary["mean_capture_ratio"],
            "scalar_hard_mean_capture_ratio": scalar_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": hard_rows["mechanism_target_ceiling"]["capture"]["summary"]["mean_capture_ratio"],
            "state_improves_scalar": improves_scalar,
            "state_improves_compatibility": improves_compat,
            "state_improves_energy": improves_energy,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "selection_scope": "non-hard eval option_error is used to fit and select the aggregate state adapter",
            "hard_eval_scope": "held-out hard episodes are used only after adapter selection",
            "feature_scope": "adapter inputs are existing non-leaky scores plus episode-level aggregate score-state summaries; hard option_error is not a feature",
            "deployment": "bounded adapter audit, not independent deployable policy evidence",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy beyond this export", "independent export validation", "complete BEDC-native world model"],
    }
    np.savez_compressed(Path(args.out), **{f"budget_{int(budget)}_score": eval_scores[int(budget)].astype(np.float32) for budget in BUDGETS})
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps({"status": "ok", "diagnosis": report["diagnosis"]}, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
