from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch

import _compute_value_model as cvm
import _compute_value_policy as cvp


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_policy_stability.json"
DEFAULT_MD = REPORT_DIR / "compute_value_policy_stability.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_policy_stability_predictions.npz"
DEFAULT_BASELINE = REPORT_DIR / "compute_value_model_predictions.npz"
BOOTSTRAPS = 1000


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


def parse_int_list(raw: str) -> list[int]:
    out = [int(item.strip()) for item in raw.split(",") if item.strip()]
    if not out:
        raise ValueError("empty integer list")
    return out


def selection_key(row: dict[str, Any]) -> tuple[float, float, float, int, int]:
    cal = row["calibration"]["allocation_delta"]
    return (
        float(cal["high"]),
        float(cal["observed"]),
        -float(row["calibration"]["mv_spearman"]),
        int(row["epochs"]),
        int(row["seed"]),
    )


def save_selected(path: Path, payload: dict[str, np.ndarray], score: np.ndarray, model_name: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    predicted_mv = cvp.scalar_to_predicted_mv(score)
    np.savez_compressed(
        path,
        episode=payload["episode"].astype(np.int64),
        t0=payload["t0"].astype(np.int64),
        anchor_ep_t0=payload["anchor_ep_t0"].astype(np.int64),
        option_depths=cvm.OPTION_DEPTHS.astype(np.int64),
        option_steps=cvm.OPTION_DEPTHS.astype(np.float64),
        uniform_steps=payload["uniform_steps"].astype(np.float64),
        option_error=payload["option_error"].astype(np.float64),
        uniform_error=payload["uniform_error"].astype(np.float64),
        true_mv=payload["true_mv"].astype(np.float64),
        predicted_mv=predicted_mv.astype(np.float64),
        policy_score=score.astype(np.float64),
        model_name=np.asarray(model_name, dtype=np.str_),
    )


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    selected = report["selected_run"]
    selected_eval = selected["eval"]["allocation_delta"]
    lines = [
        "# Compute-Value Policy Stability",
        "",
        f"- device: `{report['device']}`",
        f"- selected run: seed `{selected['seed']}`, epochs `{selected['epochs']}`",
        f"- selected eval allocation delta: `{selected_eval['observed']:.9g}` `[{selected_eval['low']:.9g}, {selected_eval['high']:.9g}]`",
        f"- oracle eval allocation delta: `{report['references']['oracle']['allocation_delta']['observed']:.9g}` `[{report['references']['oracle']['allocation_delta']['low']:.9g}, {report['references']['oracle']['allocation_delta']['high']:.9g}]`",
        f"- scalar RankNet eval allocation delta: `{report['references']['scalar_ranknet']['allocation_delta']['observed']:.9g}` `[{report['references']['scalar_ranknet']['allocation_delta']['low']:.9g}, {report['references']['scalar_ranknet']['allocation_delta']['high']:.9g}]`",
        "",
        "| seed | epochs | cal delta | eval delta | eval rho |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in report["runs"]:
        cal = row["calibration"]["allocation_delta"]
        ev = row["eval"]["allocation_delta"]
        lines.append(
            f"| {row['seed']} | {row['epochs']} | {cal['observed']:.9g} [{cal['low']:.9g}, {cal['high']:.9g}] | "
            f"{ev['observed']:.9g} [{ev['low']:.9g}, {ev['high']:.9g}] | {row['eval']['mv_spearman']:.9g} |"
        )
    lines.extend(
        [
            "",
            "The grid trains only on train episodes and uses calibration allocation delta for run selection.",
            "Eval option errors are read after policy scores are written and are used only for this diagnostic gate.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Check episode-balanced compute-value policy stability")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--baseline", default=str(DEFAULT_BASELINE))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seeds", default="3,7,11")
    parser.add_argument("--epoch-budgets", default="1,5,20,100")
    parser.add_argument("--batch", type=int, default=256)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True

    labels_path = cvm.resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS])
    latents_path = cvm.resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS])
    labels = cvm.load_npz(labels_path)
    latents = cvm.load_npz(latents_path)
    train = cvm.split_payload(labels, latents, "train")
    cal = cvm.split_payload(labels, latents, "calibration")
    eval_payload = cvm.split_payload(labels, latents, "eval")

    x_mean, x_scale = cvm.fit_standardizer(train["x"])
    x_train = cvm.apply_standardizer(train["x"], x_mean, x_scale)
    x_cal = cvm.apply_standardizer(cal["x"], x_mean, x_scale)
    x_eval = cvm.apply_standardizer(eval_payload["x"], x_mean, x_scale)

    seeds = parse_int_list(str(args.seeds))
    epoch_budgets = parse_int_list(str(args.epoch_budgets))
    runs: list[dict[str, Any]] = []
    scores: dict[tuple[int, int], np.ndarray] = {}

    for seed in seeds:
        for epochs in epoch_budgets:
            model, health = cvp.train_policy(
                train,
                cal,
                x_train,
                x_cal,
                device=device,
                seed=seed,
                hidden=int(args.hidden),
                epochs=epochs,
                batch=int(args.batch),
                lr=float(args.lr),
            )
            cal_score = cvp.predict(model, x_cal, device, int(args.batch))
            eval_score = cvp.predict(model, x_eval, device, int(args.batch))
            scores[(seed, epochs)] = eval_score
            cal_metrics = cvp.evaluate_score(cal, cal_score, seed=seed + 901)
            eval_metrics = cvp.evaluate_score(eval_payload, eval_score, seed=seed + 1009)
            runs.append(
                {
                    "seed": int(seed),
                    "epochs": int(epochs),
                    "health": health,
                    "calibration": cal_metrics,
                    "eval": eval_metrics,
                }
            )

    selected = min(runs, key=selection_key)
    selected_score = scores[(int(selected["seed"]), int(selected["epochs"]))]
    save_selected(Path(args.out), eval_payload, selected_score, "episode_balanced_policy_stability")

    oracle_score = cvp.rank_target(eval_payload)
    baseline_path = Path(args.baseline)
    baseline_score, baseline_name = cvp.baseline_from_npz(baseline_path) if baseline_path.exists() else (np.zeros(len(oracle_score)), "missing")
    references = {
        "oracle": cvp.evaluate_score(eval_payload, oracle_score, seed=8081),
        "scalar_ranknet": cvp.evaluate_score(eval_payload, baseline_score, seed=8083),
        "random_reference": cvp.random_reference(eval_payload, seed=8085),
    }
    eval_observed = np.asarray([float(row["eval"]["allocation_delta"]["observed"]) for row in runs], dtype=np.float64)
    eval_high = np.asarray([float(row["eval"]["allocation_delta"]["high"]) for row in runs], dtype=np.float64)
    eval_rho = np.asarray([float(row["eval"]["mv_spearman"]) for row in runs], dtype=np.float64)
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_policy_stability",
        "device": str(device),
        "inputs": {
            "labels": str(labels_path),
            "latents": str(latents_path),
            "baseline_prediction": str(baseline_path),
            "baseline_model": baseline_name,
        },
        "grid": {
            "seeds": seeds,
            "epoch_budgets": epoch_budgets,
            "hidden": int(args.hidden),
            "batch": int(args.batch),
            "lr": float(args.lr),
        },
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
        },
        "selection_rule": "minimize calibration allocation_delta CI high, then observed delta, then negative calibration MV Spearman",
        "selected_run": selected,
        "summary": {
            "runs": int(len(runs)),
            "eval_delta_observed_min": clean_float(float(np.min(eval_observed))),
            "eval_delta_observed_median": clean_float(float(np.median(eval_observed))),
            "eval_delta_observed_max": clean_float(float(np.max(eval_observed))),
            "eval_delta_high_min": clean_float(float(np.min(eval_high))),
            "eval_delta_high_max": clean_float(float(np.max(eval_high))),
            "eval_rho_min": clean_float(float(np.min(eval_rho))),
            "eval_rho_median": clean_float(float(np.median(eval_rho))),
            "eval_rho_max": clean_float(float(np.max(eval_rho))),
            "runs_with_eval_ci_high_below_zero": int(np.sum(eval_high < 0.0)),
        },
        "references": references,
        "runs": runs,
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only",
            "run_selection": "calibration split only",
            "eval_truth_usage": "eval option_error and true_mv used only after each policy score is produced",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(
        json.dumps(
            clean_json(
                {
                    "device": str(device),
                    "selected": {
                        "seed": selected["seed"],
                        "epochs": selected["epochs"],
                        "eval": selected["eval"],
                    },
                    "summary": report["summary"],
                    "oracle": references["oracle"],
                }
            ),
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
