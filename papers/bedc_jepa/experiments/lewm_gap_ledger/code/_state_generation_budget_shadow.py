from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_model as cvm
import _compute_value_structured_assignment as structured


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_ALLOCATION_NATIVE = REPORT_DIR / "state_generation_allocation_native_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_budget_shadow.json"
DEFAULT_MD = REPORT_DIR / "state_generation_budget_shadow.md"
DEFAULT_NPZ = REPORT_DIR / "state_generation_budget_shadow_predictions.npz"


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


def payload(episode: np.ndarray, option_error: np.ndarray) -> dict[str, np.ndarray]:
    uniform_col = int(np.where(structured.DEPTHS == 3)[0][0])
    return {
        "episode": episode.astype(np.int64),
        "option_error": option_error.astype(np.float64),
        "uniform_error": option_error[:, uniform_col].astype(np.float64),
        "true_mv": np.zeros(len(episode), dtype=np.float64),
    }


def fit_linear_map(x: np.ndarray, y: np.ndarray, alpha: float) -> np.ndarray:
    x_aug = np.concatenate([x.astype(np.float64), np.ones((len(x), 1), dtype=np.float64)], axis=1)
    eye = np.eye(x_aug.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    return np.linalg.solve(x_aug.T @ x_aug + float(alpha) * eye, x_aug.T @ y.astype(np.float64))


def apply_linear_map(x: np.ndarray, w: np.ndarray) -> np.ndarray:
    x_aug = np.concatenate([x.astype(np.float64), np.ones((len(x), 1), dtype=np.float64)], axis=1)
    return (x_aug @ w.astype(np.float64)).astype(np.float64)


def shadow_features(score: np.ndarray) -> np.ndarray:
    depths = structured.DEPTHS.astype(np.float64)
    centered_depth = (depths - 3.0) / 2.0
    per_step = score / depths[None, :]
    return np.stack(
        [
            np.min(score, axis=1),
            np.max(score, axis=1),
            np.ptp(score, axis=1),
            np.std(score, axis=1),
            np.argmin(score, axis=1).astype(np.float64),
            np.min(per_step, axis=1),
            np.max(per_step, axis=1),
            score @ centered_depth,
            score @ (centered_depth * centered_depth),
        ],
        axis=1,
    ).astype(np.float64)


def oracle_depth(episode: np.ndarray, option_error: np.ndarray) -> np.ndarray:
    choice = structured.exact_budget_choice(episode.astype(np.int64), option_error.astype(np.float64), structured.DEPTHS)
    return structured.DEPTHS[choice].astype(np.float64)


def adjust_by_depth_shadow(score: np.ndarray, shadow: np.ndarray, gamma: float) -> np.ndarray:
    depth_deviation = (structured.DEPTHS.astype(np.float64) - 3.0)[None, :]
    return (score.astype(np.float64) + float(gamma) * shadow[:, None].astype(np.float64) * depth_deviation).astype(np.float64)


def adjust_by_aggressiveness(score: np.ndarray, target_depth: np.ndarray, gamma: float) -> np.ndarray:
    desired = (target_depth.astype(np.float64) - 3.0)[:, None]
    depth_deviation = (structured.DEPTHS.astype(np.float64) - 3.0)[None, :]
    return (score.astype(np.float64) - float(gamma) * desired * depth_deviation).astype(np.float64)


def pair_accuracy(score: np.ndarray, truth: np.ndarray) -> float:
    good = 0
    total = 0
    for i in range(score.shape[1]):
        for j in range(i + 1, score.shape[1]):
            td = truth[:, i] - truth[:, j]
            sd = score[:, i] - score[:, j]
            mask = np.abs(td) > 1.0e-9
            good += int(np.sum(np.sign(td[mask]) == np.sign(sd[mask])))
            total += int(np.sum(mask))
    return clean_float(float(good / total)) if total else 0.0


def evaluate(split: dict[str, np.ndarray], score: np.ndarray, *, seed: int) -> dict[str, Any]:
    p = payload(split["episode"], split["option_error"])
    metrics = structured.evaluate_scores(p, score, seed=seed)
    metrics["pair_accuracy"] = pair_accuracy(score, split["option_error"])
    return metrics


def choose_transform(cal: dict[str, np.ndarray], eval_split: dict[str, np.ndarray], *, seed: int) -> dict[str, Any]:
    cal_features = shadow_features(cal["base_score"])
    eval_features = shadow_features(eval_split["base_score"])
    y_oracle = oracle_depth(cal["episode"], cal["option_error"])
    rows: dict[str, Any] = {}
    candidates: list[tuple[str, np.ndarray, np.ndarray]] = [("base", cal["base_score"], eval_split["base_score"])]
    for alpha in [0.001, 0.01, 0.1, 1.0, 10.0]:
        w = fit_linear_map(cal_features, y_oracle, alpha)
        cal_depth = np.clip(apply_linear_map(cal_features, w), 1.0, 5.0)
        eval_depth = np.clip(apply_linear_map(eval_features, w), 1.0, 5.0)
        for gamma in [0.25, 0.5, 1.0, 2.0]:
            candidates.append(
                (
                    f"aggressive_alpha_{alpha:g}_gamma_{gamma:g}",
                    adjust_by_aggressiveness(cal["base_score"], cal_depth, gamma),
                    adjust_by_aggressiveness(eval_split["base_score"], eval_depth, gamma),
                )
            )
    cal_shadow = apply_linear_map(cal_features, fit_linear_map(cal_features, y_oracle - 3.0, 0.1))
    eval_shadow = apply_linear_map(eval_features, fit_linear_map(cal_features, y_oracle - 3.0, 0.1))
    for gamma in [-2.0, -1.0, -0.5, 0.5, 1.0, 2.0]:
        candidates.append(
            (
                f"shadow_gamma_{gamma:g}",
                adjust_by_depth_shadow(cal["base_score"], cal_shadow, gamma),
                adjust_by_depth_shadow(eval_split["base_score"], eval_shadow, gamma),
            )
        )
    best_name = ""
    best_key = (float("inf"), float("inf"))
    best_eval_score = eval_split["base_score"]
    for offset, (name, cal_score, eval_score) in enumerate(candidates):
        metrics = evaluate(cal, cal_score, seed=seed + offset)
        rows[name] = metrics
        delta = metrics["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]))
        if key < best_key:
            best_key = key
            best_name = name
            best_eval_score = eval_score
    return {
        "selected": best_name,
        "selection_key": list(best_key),
        "calibration": rows,
        "eval_score": best_eval_score.astype(np.float64),
    }


def report_selection(selection: dict[str, Any]) -> dict[str, Any]:
    return {
        "selected": selection["selected"],
        "selection_key": selection["selection_key"],
        "calibration": selection["calibration"],
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    rows = report["eval"]
    lines = [
        "# State-Generation Budget Shadow",
        "",
        f"- selected transform: `{report['selection']['selected']}`",
        "",
        "| scorer | allocation delta | rho | pair accuracy |",
        "|---|---:|---:|---:|",
    ]
    for name in ["budget_shadow", "base_allocation_native", "oracle_true_error"]:
        row = rows[name]
        d = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {d['observed']:.6g} [{d['low']:.6g}, {d['high']:.6g}] | "
            f"{row['score_error_spearman']:.6g} | {row.get('pair_accuracy', 0.0):.6g} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Fit a budget-shadow transform for allocation-native state-generation scores")
    parser.add_argument("--allocation-native", default=str(DEFAULT_ALLOCATION_NATIVE))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--npz", default=str(DEFAULT_NPZ))
    parser.add_argument("--seed", type=int, default=353)
    args = parser.parse_args()
    with np.load(Path(args.allocation_native), allow_pickle=False) as native:
        cal = {
            "episode": native["calibration_episode"].astype(np.int64),
            "option_error": native["calibration_option_error"].astype(np.float64),
            "base_score": native["calibration_allocation_native_score"].astype(np.float64),
        }
        eval_split = {
            "episode": native["episode"].astype(np.int64),
            "option_error": native["option_error"].astype(np.float64),
            "base_score": native["allocation_native_score"].astype(np.float64),
        }
    selection = choose_transform(cal, eval_split, seed=int(args.seed))
    budget_score = selection["eval_score"]
    eval_seed = int(args.seed) + 100
    rows = {
        "budget_shadow": evaluate(eval_split, budget_score, seed=eval_seed),
        "base_allocation_native": evaluate(eval_split, eval_split["base_score"], seed=eval_seed),
        "oracle_true_error": evaluate(eval_split, eval_split["option_error"], seed=eval_seed),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_budget_shadow",
        "inputs": {"allocation_native": str(args.allocation_native)},
        "counts": {
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_split["episode"])),
            "eval_episodes": int(len(np.unique(eval_split["episode"]))),
        },
        "selection": report_selection(selection),
        "eval": rows,
        "diagnosis": {
            "allocation_closed": bool(float(rows["budget_shadow"]["allocation_delta"]["high"]) < 0.0),
            "beats_base_observed": bool(float(rows["budget_shadow"]["allocation_delta"]["observed"]) < float(rows["base_allocation_native"]["allocation_delta"]["observed"])),
            "beats_base_ci_high": bool(float(rows["budget_shadow"]["allocation_delta"]["high"]) < float(rows["base_allocation_native"]["allocation_delta"]["high"])),
            "oracle_closed": bool(float(rows["oracle_true_error"]["allocation_delta"]["high"]) < 0.0),
        },
        "leakage_attestation": {
            "training": "post-hoc budget-shadow transform only",
            "calibration": "transform family selected on calibration labels and real calibration model scores; eval labels used only for final metrics",
            "boundary": "post-hoc score transform diagnoses budget-shadow calibration and is not deployable policy evidence",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy", "allocation closure unless eval CI high < 0", "complete BEDC-native world model"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    chosen = structured.exact_budget_choice(eval_split["episode"], budget_score, structured.DEPTHS)
    np.savez_compressed(
        Path(args.npz),
        episode=eval_split["episode"].astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        base_score=eval_split["base_score"].astype(np.float64),
        budget_shadow_score=budget_score.astype(np.float64),
        chosen_depth=structured.DEPTHS[chosen].astype(np.int64),
        chosen_col=chosen.astype(np.int64),
    )
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
