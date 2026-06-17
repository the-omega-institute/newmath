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
DEFAULT_JSON = REPORT_DIR / "compute_value_structured_ablation.json"
DEFAULT_MD = REPORT_DIR / "compute_value_structured_ablation.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_structured_ablation_predictions.npz"
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


def fit_xy(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_payload: dict[str, np.ndarray],
    *,
    mode: str,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if mode == "full":
        x_mean, x_scale = structured.fit_standardizer(train["x"])
        x_train = structured.standardize(train["x"], x_mean, x_scale)
        x_cal = structured.standardize(cal["x"], x_mean, x_scale)
        x_eval = structured.standardize(eval_payload["x"], x_mean, x_scale)
        return (
            structured.expand_options(x_train, DEPTHS),
            structured.expand_options(x_cal, DEPTHS),
            structured.expand_options(x_eval, DEPTHS),
        )
    if mode == "depth_only":
        opt = structured.option_features(DEPTHS).astype(np.float32)
        return (
            np.tile(opt, (len(train["episode"]), 1)).astype(np.float32),
            np.tile(opt, (len(cal["episode"]), 1)).astype(np.float32),
            np.tile(opt, (len(eval_payload["episode"]), 1)).astype(np.float32),
        )
    if mode == "state_only":
        x_mean, x_scale = structured.fit_standardizer(train["x"])
        x_train = structured.standardize(train["x"], x_mean, x_scale)
        x_cal = structured.standardize(cal["x"], x_mean, x_scale)
        x_eval = structured.standardize(eval_payload["x"], x_mean, x_scale)
        return (
            np.repeat(x_train.astype(np.float32), len(DEPTHS), axis=0),
            np.repeat(x_cal.astype(np.float32), len(DEPTHS), axis=0),
            np.repeat(x_eval.astype(np.float32), len(DEPTHS), axis=0),
        )
    raise ValueError(f"unknown mode: {mode}")


def target_standardizer(train: dict[str, np.ndarray]) -> tuple[float, float]:
    y_mean = float(np.mean(train["option_error"].reshape(-1)))
    y_scale = float(np.std(train["option_error"].reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    return y_mean, y_scale


def scaled_target(payload: dict[str, np.ndarray], y_mean: float, y_scale: float) -> np.ndarray:
    return ((payload["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)


def train_variant(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_payload: dict[str, np.ndarray],
    *,
    mode: str,
    device: torch.device,
    seed: int,
    epochs: int,
    hidden: int,
    batch: int,
    lr: float,
) -> tuple[dict[str, Any], np.ndarray, np.ndarray]:
    x_train, x_cal, x_eval = fit_xy(train, cal, eval_payload, mode=mode)
    y_mean, y_scale = target_standardizer(train)
    y_train = scaled_target(train, y_mean, y_scale)
    y_cal = scaled_target(cal, y_mean, y_scale)
    model, health = structured.train_mlp(
        x_train,
        y_train,
        train["option_error"],
        x_cal,
        y_cal,
        cal,
        device=device,
        seed=seed,
        hidden=hidden,
        epochs=epochs,
        batch=batch,
        lr=lr,
    )
    cal_score = structured.reshape_scores(structured.predict_mlp(model, x_cal, device, batch) * y_scale + y_mean, len(cal["episode"]))
    eval_score = structured.reshape_scores(
        structured.predict_mlp(model, x_eval, device, batch) * y_scale + y_mean,
        len(eval_payload["episode"]),
    )
    row = {
        "mode": mode,
        "health": health,
        "calibration": structured.evaluate_scores(cal, cal_score, seed=seed + 2101),
        "eval": structured.evaluate_scores(eval_payload, eval_score, seed=seed + 2201),
    }
    choice = structured.exact_budget_choice(eval_payload["episode"], eval_score, DEPTHS)
    return row, eval_score, choice


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Structured Ablation",
        "",
        f"- device: `{report['device']}`",
        f"- seed: `{report['grid']['seed']}`",
        f"- epochs: `{report['grid']['epochs']}`",
        "",
        "| row | eval allocation delta | score/error rho |",
        "|---|---:|---:|",
    ]
    order = ["full", "state_only", "depth_only", "ridge_full", "refined_mv_dp", "policy_score_balanced", "exact_budget_oracle"]
    for name in order:
        row = report["rows"][name]
        d = row["eval"]["allocation_delta"]
        rho = row["eval"].get("score_error_spearman", row["eval"].get("policy_target_spearman", 0.0))
        lines.append(f"| `{name}` | {d['observed']:.9g} [{d['low']:.9g}, {d['high']:.9g}] | {rho:.9g} |")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Ablate option-conditioned exact-budget compute-value assignment")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=41)
    parser.add_argument("--epochs", type=int, default=420)
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

    rows: dict[str, Any] = {}
    predicted: dict[str, np.ndarray] = {}
    choices: dict[str, np.ndarray] = {}
    for mode in ["full", "state_only", "depth_only"]:
        row, score, choice = train_variant(
            train,
            cal,
            eval_payload,
            mode=mode,
            device=device,
            seed=int(args.seed),
            epochs=int(args.epochs),
            hidden=int(args.hidden),
            batch=int(args.batch),
            lr=float(args.lr),
        )
        rows[mode] = row
        predicted[mode] = score
        choices[mode] = choice

    x_train, x_cal, x_eval = fit_xy(train, cal, eval_payload, mode="full")
    y_mean, y_scale = target_standardizer(train)
    y_train = scaled_target(train, y_mean, y_scale)
    ridge_w, ridge_b = structured.train_ridge(x_train, y_train, alpha=10.0)
    ridge_eval = structured.reshape_scores(structured.predict_ridge(x_eval, ridge_w, ridge_b) * y_scale + y_mean, len(eval_payload["episode"]))
    rows["ridge_full"] = {
        "mode": "ridge_full",
        "eval": structured.evaluate_scores(eval_payload, ridge_eval, seed=int(args.seed) + 2301),
    }
    rows["refined_mv_dp"] = {
        "mode": "refined_mv_dp",
        "eval": structured.refined_reference(eval_payload, structured.REFINED_PRED, seed=int(args.seed) + 2303),
    }
    rows["policy_score_balanced"] = {
        "mode": "policy_score_balanced",
        "eval": structured.balanced_policy_reference(eval_payload, structured.POLICY_PRED, seed=int(args.seed) + 2305),
    }
    rows["exact_budget_oracle"] = {
        "mode": "exact_budget_oracle",
        "eval": structured.exact_oracle(eval_payload, seed=int(args.seed) + 2307),
    }

    selected = "full"
    structured.write_npz(Path(args.out), eval_payload, predicted[selected], choices[selected], "structured_ablation_full")
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_structured_ablation",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
        "grid": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
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
        "rows": rows,
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only for rows that use state features",
            "target_standardizer": "fit on train option_error only",
            "model_selection": "each neural row uses calibration split exact-budget allocation only",
            "eval_truth_usage": "eval option_error used only after predicted option scores are produced",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"device": str(device), "rows": {k: v["eval"] for k, v in rows.items()}}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
