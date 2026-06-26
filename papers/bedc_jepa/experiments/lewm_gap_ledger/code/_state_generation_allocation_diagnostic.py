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
DEFAULT_PRED = REPORT_DIR / "state_generation_candidate_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_allocation_diagnostic.json"
DEFAULT_MD = REPORT_DIR / "state_generation_allocation_diagnostic.md"
DEFAULT_NPZ = REPORT_DIR / "state_generation_allocation_diagnostic.npz"


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


def payload_from_archive(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    depths = structured.DEPTHS.astype(np.int64)
    uniform_col = int(np.where(depths == 3)[0][0])
    return {
        "episode": data["episode"].astype(np.int64),
        "option_error": data["option_error"].astype(np.float64),
        "uniform_error": data["option_error"][:, uniform_col].astype(np.float64),
        "true_mv": np.zeros(len(data["episode"]), dtype=np.float64),
    }


def center_rows(x: np.ndarray) -> np.ndarray:
    return (x.astype(np.float64) - np.mean(x.astype(np.float64), axis=1, keepdims=True)).astype(np.float64)


def bias_correct(pred: np.ndarray, truth: np.ndarray) -> np.ndarray:
    return (pred.astype(np.float64) - np.mean(pred.astype(np.float64) - truth.astype(np.float64), axis=0, keepdims=True)).astype(np.float64)


def linear_calibrate(pred: np.ndarray, truth: np.ndarray) -> np.ndarray:
    x = pred.reshape(-1).astype(np.float64)
    y = truth.reshape(-1).astype(np.float64)
    x_mean = float(np.mean(x))
    y_mean = float(np.mean(y))
    denom = float(np.sum((x - x_mean) ** 2))
    slope = 0.0 if denom <= 1.0e-12 else float(np.sum((x - x_mean) * (y - y_mean)) / denom)
    intercept = y_mean - slope * x_mean
    return (slope * pred.astype(np.float64) + intercept).astype(np.float64)


def per_anchor_rank_score(pred: np.ndarray) -> np.ndarray:
    out = np.zeros_like(pred, dtype=np.float64)
    for row in range(pred.shape[0]):
        order = np.argsort(pred[row], kind="mergesort")
        ranks = np.zeros(pred.shape[1], dtype=np.float64)
        ranks[order] = np.arange(pred.shape[1], dtype=np.float64)
        out[row] = ranks
    return out


def option_pair_accuracy(score: np.ndarray, truth: np.ndarray) -> float:
    good = 0
    total = 0
    for i in range(score.shape[1]):
        for j in range(i + 1, score.shape[1]):
            true_diff = truth[:, i] - truth[:, j]
            score_diff = score[:, i] - score[:, j]
            mask = np.abs(true_diff) > 1.0e-9
            if not np.any(mask):
                continue
            good += int(np.sum(np.sign(true_diff[mask]) == np.sign(score_diff[mask])))
            total += int(np.sum(mask))
    return clean_float(float(good / total)) if total else 0.0


def regret_summary(payload: dict[str, np.ndarray], chosen: np.ndarray) -> dict[str, float]:
    option_error = payload["option_error"]
    selected = option_error[np.arange(len(chosen)), chosen.astype(np.int64)]
    oracle = option_error[np.arange(len(chosen)), np.argmin(option_error, axis=1)]
    uniform_col = int(np.where(structured.DEPTHS == 3)[0][0])
    uniform = option_error[:, uniform_col]
    return {
        "selected_minus_uniform_mean": clean_float(float(np.mean(selected - uniform))),
        "selected_minus_per_anchor_oracle_mean": clean_float(float(np.mean(selected - oracle))),
        "per_anchor_improvement_rate": clean_float(float(np.mean(selected < uniform))),
    }


def evaluate_variant(payload: dict[str, np.ndarray], score: np.ndarray, *, seed: int) -> dict[str, Any]:
    metrics = structured.evaluate_scores(payload, score.astype(np.float64), seed=seed)
    chosen = structured.exact_budget_choice(payload["episode"], score.astype(np.float64), structured.DEPTHS)
    metrics["pair_accuracy"] = option_pair_accuracy(score, payload["option_error"])
    metrics["regret"] = regret_summary(payload, chosen)
    return metrics


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Allocation Diagnostic",
        "",
        f"- anchors: `{report['counts']['anchors']}`",
        f"- episodes: `{report['counts']['episodes']}`",
        "",
        "| score variant | allocation delta | rho | pair accuracy | chosen depths |",
        "|---|---:|---:|---:|---|",
    ]
    for name, row in report["variants"].items():
        d = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {d['observed']:.6g} [{d['low']:.6g}, {d['high']:.6g}] | "
            f"{row['score_error_spearman']:.6g} | {row['pair_accuracy']:.6g} | "
            f"`{row['chosen_depth_counts']}` |"
        )
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Diagnose why state-generation option scores do not close allocation")
    parser.add_argument("--predictions", default=str(DEFAULT_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--npz", default=str(DEFAULT_NPZ))
    parser.add_argument("--seed", type=int, default=233)
    args = parser.parse_args()
    with np.load(Path(args.predictions), allow_pickle=False) as archive:
        data = {key: archive[key] for key in archive.files}
    payload = payload_from_archive(data)
    pred = data["predicted_option_error"].astype(np.float64)
    truth = data["option_error"].astype(np.float64)
    variants = {
        "raw_predicted_error": pred,
        "negated_predicted_error": -pred,
        "row_centered_predicted_error": center_rows(pred),
        "row_centered_truth": center_rows(truth),
        "bias_corrected_predicted_error": bias_correct(pred, truth),
        "linear_calibrated_predicted_error": linear_calibrate(pred, truth),
        "per_anchor_rank_predicted_error": per_anchor_rank_score(pred),
        "oracle_true_error": truth,
    }
    eval_rows: dict[str, Any] = {}
    chosen_payload: dict[str, np.ndarray] = {
        "episode": payload["episode"].astype(np.int64),
        "option_error": truth.astype(np.float64),
        "predicted_option_error": pred.astype(np.float64),
        "option_depths": structured.DEPTHS.astype(np.int64),
    }
    for offset, (name, score) in enumerate(variants.items()):
        eval_rows[name] = evaluate_variant(payload, score, seed=int(args.seed) + offset)
        chosen_payload[f"{name}_score"] = score.astype(np.float64)
        chosen_payload[f"{name}_chosen_depth"] = structured.DEPTHS[
            structured.exact_budget_choice(payload["episode"], score, structured.DEPTHS)
        ].astype(np.int64)
    raw = eval_rows["raw_predicted_error"]
    oracle = eval_rows["oracle_true_error"]
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_allocation_diagnostic",
        "inputs": {"predictions": str(args.predictions)},
        "counts": {
            "anchors": int(len(payload["episode"])),
            "episodes": int(len(np.unique(payload["episode"]))),
        },
        "variants": eval_rows,
        "diagnosis": {
            "raw_score_has_global_rank_signal": bool(float(raw["score_error_spearman"]) > 0.5),
            "raw_allocation_closed": bool(float(raw["allocation_delta"]["high"]) < 0.0),
            "oracle_allocation_closed": bool(float(oracle["allocation_delta"]["high"]) < 0.0),
            "interpretation": (
                "The fixed candidate score is useful only if its exact-budget DP allocation delta has CI high below zero. "
                "Global score/error correlation alone is not sufficient evidence for allocation closure."
            ),
        },
        "leakage_attestation": {
            "training": "no model is trained in this diagnostic",
            "eval_truth_usage": "eval option_error is used only for post-hoc score transforms and oracle/boundary diagnostics",
            "claim_boundary": "truth-calibrated variants are diagnostics and are not deployable policy scores",
            "slurm_or_ssh": "not used",
        },
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    np.savez_compressed(Path(args.npz), **chosen_payload)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
