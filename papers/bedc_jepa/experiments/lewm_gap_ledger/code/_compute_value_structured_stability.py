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
import _compute_value_refined_option_model as refined
import _compute_value_structured_assignment as structured


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_structured_stability.json"
DEFAULT_MD = REPORT_DIR / "compute_value_structured_stability.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_structured_stability_predictions.npz"
DEPTHS = structured.DEPTHS


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


def run_key(row: dict[str, Any]) -> tuple[float, float, float, int, int]:
    cal = row["calibration"]["allocation_delta"]
    return (
        float(cal["high"]),
        float(cal["observed"]),
        -float(row["calibration"]["score_error_spearman"]),
        int(row["epochs"]),
        int(row["seed"]),
    )


def write_selected(path: Path, payload: dict[str, np.ndarray], option_score: np.ndarray, chosen: np.ndarray, model_name: str) -> None:
    structured.write_npz(path, payload, option_score, chosen, model_name)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    selected = report["selected_run"]
    selected_delta = selected["eval"]["allocation_delta"]
    summary = report["summary"]
    oracle = report["references"]["exact_budget_oracle"]["allocation_delta"]
    lines = [
        "# Compute-Value Structured Stability",
        "",
        f"- device: `{report['device']}`",
        f"- selected run: seed `{selected['seed']}`, epochs `{selected['epochs']}`",
        f"- selected eval allocation delta: `{selected_delta['observed']:.9g}` `[{selected_delta['low']:.9g}, {selected_delta['high']:.9g}]`",
        f"- runs with eval CI high below zero: `{summary['runs_with_eval_ci_high_below_zero']}` / `{summary['runs']}`",
        f"- exact-budget oracle delta: `{oracle['observed']:.9g}` `[{oracle['low']:.9g}, {oracle['high']:.9g}]`",
        "",
        "| seed | epochs | cal delta | eval delta | eval score/error rho |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in report["runs"]:
        cal = row["calibration"]["allocation_delta"]
        ev = row["eval"]["allocation_delta"]
        lines.append(
            f"| {row['seed']} | {row['epochs']} | {cal['observed']:.9g} [{cal['low']:.9g}, {cal['high']:.9g}] | "
            f"{ev['observed']:.9g} [{ev['low']:.9g}, {ev['high']:.9g}] | {row['eval']['score_error_spearman']:.9g} |"
        )
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Check option-conditioned exact-budget assignment stability")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seeds", default="29,41,53")
    parser.add_argument("--epoch-budgets", default="160,280,420")
    parser.add_argument("--hidden", type=int, default=384)
    parser.add_argument("--batch", type=int, default=512)
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
    train = refined.split_payload(labels, latents, "train")
    cal = refined.split_payload(labels, latents, "calibration")
    eval_payload = refined.split_payload(labels, latents, "eval")
    x_mean, x_scale = structured.fit_standardizer(train["x"])
    x_train = structured.standardize(train["x"], x_mean, x_scale)
    x_cal = structured.standardize(cal["x"], x_mean, x_scale)
    x_eval = structured.standardize(eval_payload["x"], x_mean, x_scale)
    ex_train = structured.expand_options(x_train, DEPTHS)
    ex_cal = structured.expand_options(x_cal, DEPTHS)
    ex_eval = structured.expand_options(x_eval, DEPTHS)
    y_mean = float(np.mean(train["option_error"].reshape(-1)))
    y_scale = float(np.std(train["option_error"].reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    y_train = ((train["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)
    y_cal = ((cal["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)

    runs: list[dict[str, Any]] = []
    scores: dict[tuple[int, int], np.ndarray] = {}
    choices: dict[tuple[int, int], np.ndarray] = {}
    seeds = parse_int_list(str(args.seeds))
    epoch_budgets = parse_int_list(str(args.epoch_budgets))
    for seed in seeds:
        for epochs in epoch_budgets:
            model, health = structured.train_mlp(
                ex_train,
                y_train,
                train["option_error"],
                ex_cal,
                y_cal,
                cal,
                device=device,
                seed=seed,
                hidden=int(args.hidden),
                epochs=epochs,
                batch=int(args.batch),
                lr=float(args.lr),
            )
            cal_score = structured.reshape_scores(
                structured.predict_mlp(model, ex_cal, device, int(args.batch)) * y_scale + y_mean,
                len(cal["episode"]),
            )
            eval_score = structured.reshape_scores(
                structured.predict_mlp(model, ex_eval, device, int(args.batch)) * y_scale + y_mean,
                len(eval_payload["episode"]),
            )
            eval_choice = structured.exact_budget_choice(eval_payload["episode"], eval_score, DEPTHS)
            scores[(seed, epochs)] = eval_score
            choices[(seed, epochs)] = eval_choice
            runs.append(
                {
                    "seed": int(seed),
                    "epochs": int(epochs),
                    "health": health,
                    "calibration": structured.evaluate_scores(cal, cal_score, seed=seed + 1201),
                    "eval": structured.evaluate_scores(eval_payload, eval_score, seed=seed + 1301),
                }
            )

    selected = min(runs, key=run_key)
    selected_key = (int(selected["seed"]), int(selected["epochs"]))
    write_selected(Path(args.out), eval_payload, scores[selected_key], choices[selected_key], "option_conditioned_exact_budget_stability")

    eval_observed = np.asarray([float(row["eval"]["allocation_delta"]["observed"]) for row in runs], dtype=np.float64)
    eval_high = np.asarray([float(row["eval"]["allocation_delta"]["high"]) for row in runs], dtype=np.float64)
    eval_rho = np.asarray([float(row["eval"]["score_error_spearman"]) for row in runs], dtype=np.float64)
    references = {
        "exact_budget_oracle": structured.exact_oracle(eval_payload, seed=1701),
        "refined_mv_dp": structured.refined_reference(eval_payload, structured.REFINED_PRED, seed=1703),
        "policy_score_balanced": structured.balanced_policy_reference(eval_payload, structured.POLICY_PRED, seed=1705),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_structured_stability",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
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
        "selection_rule": "minimize calibration exact-budget allocation_delta CI high, then observed delta, then negative score/error Spearman",
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
            "target_standardizer": "fit on train option_error only",
            "run_selection": "calibration split only",
            "eval_truth_usage": "eval option_error used only after each predicted option score is produced",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"device": str(device), "selected_run": selected, "summary": report["summary"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
