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
import _compute_value_structured_assignment as structured
import _compute_value_refined_option_model as refined


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_LABELS = Path("C:/OMEGA/le-wm-survey/reports/crossenv_horizon_labels_pusht.npz")
DEFAULT_LATENTS = Path("C:/OMEGA/le-wm-survey/pusht_latent_large.npz")
DEFAULT_JSON = REPORT_DIR / "compute_value_independent_full_feature.json"
DEFAULT_MD = REPORT_DIR / "compute_value_independent_full_feature.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_independent_full_feature_predictions.npz"
DEPTHS = structured.DEPTHS
REQUIRED_LATENT = ("emb", "action", "pred")
REQUIRED_LABEL_SUFFIXES = ("anchor_ep_t0", "valid", "pred_z", "err_at_h")
SPLITS = ("train", "calibration", "eval")


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


def inspect_npz(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"path": str(path), "exists": False, "readable": False, "keys": [], "shapes": {}}
    try:
        with np.load(path, allow_pickle=False) as data:
            keys = sorted(data.files)
            shapes = {key: list(data[key].shape) for key in keys}
            dtypes = {key: str(data[key].dtype) for key in keys}
    except Exception as exc:
        return {"path": str(path), "exists": True, "readable": False, "error": str(exc), "keys": [], "shapes": {}}
    return {"path": str(path), "exists": True, "readable": True, "keys": keys, "shapes": shapes, "dtypes": dtypes}


def validate_inputs(labels: dict[str, np.ndarray], latents: dict[str, np.ndarray]) -> list[str]:
    missing: list[str] = []
    for key in REQUIRED_LATENT:
        if key not in latents:
            missing.append(f"latents:{key}")
    for key in ("horizons",):
        if key not in labels:
            missing.append(f"labels:{key}")
    for split in SPLITS:
        for suffix in REQUIRED_LABEL_SUFFIXES:
            key = f"{split}_{suffix}"
            if key not in labels:
                missing.append(f"labels:{key}")
    if missing:
        return missing
    emb = latents["emb"]
    action = latents["action"]
    pred = latents["pred"]
    if emb.ndim != 3:
        missing.append("latents:emb must be rank-3 episode/time/latent")
    if action.ndim != 3:
        missing.append("latents:action must be rank-3 episode/time/action")
    if pred.ndim != 3:
        missing.append("latents:pred must be rank-3 episode/time/latent")
    if not missing and (emb.shape[0] != action.shape[0] or emb.shape[0] != pred.shape[0]):
        missing.append("latents:episode count mismatch across emb/action/pred")
    if not missing and emb.shape[1] != action.shape[1]:
        missing.append("latents:time length mismatch between emb and action")
    if not missing and pred.shape[-1] != emb.shape[-1]:
        missing.append("latents:pred latent dimension mismatch with emb")
    if not missing:
        n_ep = int(emb.shape[0])
        for split in SPLITS:
            anchors = labels[f"{split}_anchor_ep_t0"]
            if anchors.ndim != 2 or anchors.shape[1] != 2:
                missing.append(f"labels:{split}_anchor_ep_t0 must be rank-2 [n,2]")
                continue
            if len(anchors) == 0:
                missing.append(f"labels:{split}_anchor_ep_t0 is empty")
                continue
            max_ep = int(np.max(anchors[:, 0]))
            if max_ep >= n_ep:
                missing.append(f"labels:{split}_anchor_ep_t0 episode {max_ep} exceeds latent episode count {n_ep}")
    return missing


def fail_closed_report(
    *,
    labels_path: Path,
    latents_path: Path,
    labels_info: dict[str, Any],
    latents_info: dict[str, Any],
    missing: list[str],
    start: float,
    args: argparse.Namespace,
) -> dict[str, Any]:
    return {
        "status": "fail-closed",
        "schema_id": "bedc_jepa.compute_value_independent_full_feature",
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
        "input_inspection": {"labels": labels_info, "latents": latents_info},
        "missing_or_invalid": missing,
        "target": {
            "option_depths": DEPTHS.tolist(),
            "assignment_rule": "exact per-episode budget sum(depth)=3*episode_anchor_count using dynamic programming",
            "feature_scope": "base latent/action window plus predicted rollout-internal features",
        },
        "not_claimed": (
            "No independent full-feature structured compute-value replication is claimed unless "
            "the independent export supplies aligned emb, action, pred, and split horizon-label arrays."
        ),
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }


def train_row(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_payload: dict[str, np.ndarray],
    *,
    device: torch.device,
    seed: int,
    epochs: int,
    hidden: int,
    batch: int,
    lr: float,
) -> tuple[dict[str, Any], np.ndarray, np.ndarray]:
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
    model, health = structured.train_mlp(
        ex_train,
        y_train,
        train["option_error"],
        ex_cal,
        y_cal,
        cal,
        device=device,
        seed=seed,
        hidden=hidden,
        epochs=epochs,
        batch=batch,
        lr=lr,
    )
    eval_score = structured.reshape_scores(
        structured.predict_mlp(model, ex_eval, device, batch) * y_scale + y_mean,
        len(eval_payload["episode"]),
    )
    choice = structured.exact_budget_choice(eval_payload["episode"], eval_score, DEPTHS)
    report = {
        "calibration": health["best"]["calibration"],
        "eval": structured.evaluate_scores(eval_payload, eval_score, seed=seed + 1001),
        "references": {
            "exact_budget_oracle": structured.exact_oracle(eval_payload, seed=seed + 1003),
            "per_step_oracle": structured.per_step_oracle(eval_payload, seed=seed + 1005),
        },
        "health": health,
    }
    return report, eval_score, choice


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = ["# Compute-Value Independent Full-Feature", ""]
    lines.append(f"- status: `{report['status']}`")
    lines.append(f"- labels: `{report['inputs']['labels']}`")
    lines.append(f"- latents: `{report['inputs']['latents']}`")
    if report["status"] != "ok":
        missing = ", ".join(report.get("missing_or_invalid", []))
        lines.append(f"- missing or invalid: `{missing}`")
        lines.append("")
        lines.append(report["not_claimed"])
    else:
        learned = report["eval"]["learned_full_feature"]["allocation_delta"]
        exact = report["eval"]["exact_budget_oracle"]["allocation_delta"]
        lines.extend(
            [
                f"- device: `{report['device']}`",
                f"- eval anchors: `{report['counts']['eval']}` across `{report['counts']['eval_episodes']}` episodes",
                f"- learned full-feature delta: `{learned['observed']:.9g}` `[{learned['low']:.9g}, {learned['high']:.9g}]`",
                f"- exact-budget oracle delta: `{exact['observed']:.9g}` `[{exact['low']:.9g}, {exact['high']:.9g}]`",
                "",
                "This is an independent-export full-feature structured compute-value test.",
            ]
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Run independent-export full-feature structured compute-value assignment")
    parser.add_argument("--labels", default=str(DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=41)
    parser.add_argument("--epochs", type=int, default=320)
    parser.add_argument("--hidden", type=int, default=384)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    labels_path = Path(args.labels)
    latents_path = Path(args.latents)
    labels_info = inspect_npz(labels_path)
    latents_info = inspect_npz(latents_path)
    missing: list[str] = []
    labels: dict[str, np.ndarray] = {}
    latents: dict[str, np.ndarray] = {}
    if not labels_info.get("readable", False):
        missing.append("labels artifact is missing or unreadable")
    else:
        labels = load_npz(labels_path)
    if not latents_info.get("readable", False):
        missing.append("latents artifact is missing or unreadable")
    else:
        latents = load_npz(latents_path)
    if not missing:
        missing = validate_inputs(labels, latents)
    if missing:
        report = fail_closed_report(
            labels_path=labels_path,
            latents_path=latents_path,
            labels_info=labels_info,
            latents_info=latents_info,
            missing=missing,
            start=start,
            args=args,
        )
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
        write_markdown(Path(args.md), report)
        print(json.dumps(clean_json({"status": report["status"], "missing_or_invalid": missing}), ensure_ascii=False, sort_keys=True))
        return 0

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    train = refined.split_payload(labels, latents, "train")
    cal = refined.split_payload(labels, latents, "calibration")
    eval_payload = refined.split_payload(labels, latents, "eval")
    row, eval_score, choice = train_row(
        train,
        cal,
        eval_payload,
        device=device,
        seed=int(args.seed),
        epochs=int(args.epochs),
        hidden=int(args.hidden),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    structured.write_npz(Path(args.out), eval_payload, eval_score, choice, "independent_full_feature_exact_budget")
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_independent_full_feature",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
            "feature_dim": int(train["x"].shape[1]),
        },
        "target": {
            "option_depths": DEPTHS.tolist(),
            "assignment_rule": "exact per-episode budget sum(depth)=3*episode_anchor_count using dynamic programming",
            "feature_scope": "independent export base latent/action window plus predicted rollout-internal features",
        },
        "calibration": {"learned_full_feature": row["calibration"]},
        "eval": {
            "learned_full_feature": row["eval"],
            "exact_budget_oracle": row["references"]["exact_budget_oracle"],
            "per_step_oracle": row["references"]["per_step_oracle"],
        },
        "health": row["health"],
        "leakage_attestation": {
            "features": "built from aligned emb/action/pred carrier, split pred_z, valid masks, and anchor timing",
            "labels": "err_at_h is used only for option_error targets and final evaluation",
            "feature_standardizer": "fit on train full features only",
            "target_standardizer": "fit on train option_error only",
            "model_selection": "calibration split exact-budget allocation only",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"status": report["status"], "device": str(device), "eval": report["eval"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
