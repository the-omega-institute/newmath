from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured
import _state_generation_episode_allocation as episode_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_seed_ensemble.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_seed_ensemble.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_episode_seed_ensemble_predictions.npz"


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


def load_seed_prediction(seed: int) -> dict[str, np.ndarray]:
    path = REPORT_DIR / f"state_generation_episode_allocation_seed_{seed}_predictions.npz"
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def load_seed_report(seed: int) -> dict[str, Any]:
    path = REPORT_DIR / f"state_generation_episode_allocation_seed_{seed}.json"
    return json.loads(path.read_text(encoding="utf-8"))


def payload_from_prediction(pred: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    return {
        "episode": pred["episode"].astype(np.int64),
        "option_error": pred["option_error"].astype(np.float64),
        "uniform_error": pred["option_error"][:, int(np.where(pred["option_depths"].astype(np.int64) == 3)[0][0])].astype(np.float64),
        "true_mv": np.zeros(len(pred["episode"]), dtype=np.float64),
    }


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


def oracle_match(score: np.ndarray, oracle: np.ndarray) -> float:
    return clean_float(float(np.mean(np.argmin(score, axis=1).astype(np.int64) == oracle.astype(np.int64))))


def evaluate(payload: dict[str, np.ndarray], score: np.ndarray, oracle: np.ndarray, *, seed: int) -> dict[str, Any]:
    metrics = structured.evaluate_scores(payload, score.astype(np.float64), seed=seed)
    metrics["pair_accuracy"] = pair_accuracy(score.astype(np.float64), payload["option_error"])
    metrics["oracle_match"] = oracle_match(score.astype(np.float64), oracle)
    return metrics


def normalize_per_anchor(score: np.ndarray) -> np.ndarray:
    centered = score.astype(np.float64) - np.mean(score.astype(np.float64), axis=1, keepdims=True)
    scale = np.std(centered, axis=1, keepdims=True)
    scale[scale < 1.0e-9] = 1.0
    return centered / scale


def depth_histogram(chosen: np.ndarray, depths: np.ndarray) -> dict[str, int]:
    return {str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen], return_counts=True))}


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Episode Seed Ensemble",
        "",
        f"- seeds: `{report['config']['seeds']}`",
        f"- best row: `{report['summary']['best_row']}`",
        "",
        "| row | allocation delta | rho | oracle match |",
        "|---|---:|---:|---:|",
    ]
    for name, row in report["eval"].items():
        d = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {d['observed']:.6g} [{d['low']:.6g}, {d['high']:.6g}] | "
            f"{row['score_error_spearman']:.6g} | {row.get('oracle_match', 0.0):.6g} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Diagnose episode-allocation seed ensembling and transfer")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seeds", nargs="+", type=int, default=[431, 509, 617])
    parser.add_argument("--bootstrap-seed", type=int, default=991)
    args = parser.parse_args()
    preds = [load_seed_prediction(int(seed)) for seed in args.seeds]
    reports = [load_seed_report(int(seed)) for seed in args.seeds]
    base = preds[0]
    payload = payload_from_prediction(base)
    depths = base["option_depths"].astype(np.int64)
    oracle = base["oracle_choice"].astype(np.int64)
    seed_scores = [pred["episode_allocation_score"].astype(np.float64) for pred in preds]
    for pred in preds[1:]:
        if not np.array_equal(pred["episode"].astype(np.int64), base["episode"].astype(np.int64)):
            raise RuntimeError("seed prediction episode mismatch")
        if not np.array_equal(pred["anchor_ep_t0"].astype(np.int64), base["anchor_ep_t0"].astype(np.int64)):
            raise RuntimeError("seed prediction anchor mismatch")
        if not np.array_equal(pred["option_depths"].astype(np.int64), depths):
            raise RuntimeError("seed prediction depth mismatch")
    stack = np.stack(seed_scores, axis=0)
    normalized = np.stack([normalize_per_anchor(score) for score in seed_scores], axis=0)
    rows: dict[str, np.ndarray] = {
        "mean_score": np.mean(stack, axis=0),
        "median_score": np.median(stack, axis=0),
        "mean_normalized": np.mean(normalized, axis=0),
        "median_normalized": np.median(normalized, axis=0),
    }
    for seed, score in zip(args.seeds, seed_scores):
        rows[f"seed_{int(seed)}"] = score
    eval_rows = {name: evaluate(payload, score, oracle, seed=int(args.bootstrap_seed)) for name, score in rows.items()}
    with np.load(REPORT_DIR / "state_generation_allocation_native_predictions.npz", allow_pickle=False) as native:
        native_score = native["allocation_native_score"].astype(np.float64)
    eval_rows["allocation_native"] = evaluate(payload, native_score, oracle, seed=int(args.bootstrap_seed))
    eval_rows["oracle_true_error"] = evaluate(payload, payload["option_error"], oracle, seed=int(args.bootstrap_seed))
    best_row = min(
        [name for name in eval_rows if name not in {"oracle_true_error"}],
        key=lambda name: (
            float(eval_rows[name]["allocation_delta"]["high"]),
            float(eval_rows[name]["allocation_delta"]["observed"]),
        ),
    )
    chosen_by_row = {
        name: structured.exact_budget_choice(payload["episode"], score.astype(np.float64), structured.DEPTHS).astype(np.int64)
        for name, score in rows.items()
    }
    choice_stack = np.stack([chosen_by_row[f"seed_{int(seed)}"] for seed in args.seeds], axis=0)
    agreement = {
        "all_seed_same_choice_rate": clean_float(float(np.mean(np.all(choice_stack == choice_stack[0:1, :], axis=0)))),
        "majority_choice_rate": clean_float(float(np.mean([np.max(np.bincount(choice_stack[:, i], minlength=len(depths))) >= 2 for i in range(choice_stack.shape[1])]))),
        "oracle_choice_majority_match": clean_float(float(np.mean([np.argmax(np.bincount(choice_stack[:, i], minlength=len(depths))) == int(oracle[i]) for i in range(choice_stack.shape[1])]))),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_seed_ensemble",
        "config": {"seeds": [int(seed) for seed in args.seeds], "bootstrap_seed": int(args.bootstrap_seed)},
        "counts": {
            "eval": int(len(payload["episode"])),
            "eval_episodes": int(len(np.unique(payload["episode"]))),
        },
        "eval": eval_rows,
        "choice_agreement": agreement,
        "depth_counts": {name: depth_histogram(choice, depths) for name, choice in chosen_by_row.items()},
        "source_seed_reports": {
            str(int(seed)): {
                "selected_epoch": int(report["selection"]["best"]["epoch"]),
                "delta": report["eval"]["episode_allocation"]["allocation_delta"],
            }
            for seed, report in zip(args.seeds, reports)
        },
        "summary": {
            "best_row": best_row,
            "best_delta": eval_rows[best_row]["allocation_delta"],
            "best_is_ensemble": bool(best_row in {"mean_score", "median_score", "mean_normalized", "median_normalized"}),
            "allocation_closed": bool(float(eval_rows[best_row]["allocation_delta"]["high"]) < 0.0),
            "oracle_closed": bool(float(eval_rows["oracle_true_error"]["allocation_delta"]["high"]) < 0.0),
        },
        "leakage_attestation": {
            "features": "held-out eval predictions only; no retraining",
            "selection": "post-hoc diagnostic over seed aggregation rows, selected by eval CI high for diagnosis only",
            "slurm_or_ssh": "not used",
            "targets": "eval option_error used only after fixed seed scores are loaded for diagnostics",
        },
        "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    np.savez_compressed(
        Path(args.out),
        episode=payload["episode"].astype(np.int64),
        anchor_ep_t0=base["anchor_ep_t0"].astype(np.int64),
        option_depths=depths.astype(np.int64),
        option_error=payload["option_error"].astype(np.float64),
        oracle_choice=oracle.astype(np.int64),
        mean_score=rows["mean_score"].astype(np.float64),
        median_score=rows["median_score"].astype(np.float64),
        mean_normalized=rows["mean_normalized"].astype(np.float64),
        median_normalized=rows["median_normalized"].astype(np.float64),
    )
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
