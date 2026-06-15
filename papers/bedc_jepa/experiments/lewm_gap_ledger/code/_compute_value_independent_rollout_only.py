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


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_LABELS = Path("C:/OMEGA/le-wm-survey/reports/crossenv_horizon_labels_pusht.npz")
DEFAULT_JSON = REPORT_DIR / "compute_value_independent_rollout_only.json"
DEFAULT_MD = REPORT_DIR / "compute_value_independent_rollout_only.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_independent_rollout_only_predictions.npz"
DEPTHS = structured.DEPTHS
MAX_H = 5


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


def horizon_indices(labels: dict[str, np.ndarray], depths: np.ndarray) -> list[int]:
    horizons = [int(item) for item in labels["horizons"].reshape(-1)]
    missing = [int(depth) for depth in depths if int(depth) not in horizons]
    if missing:
        raise RuntimeError(f"missing horizons: {missing}")
    return [horizons.index(int(depth)) for depth in depths]


def safe_norm(x: np.ndarray, axis: int) -> np.ndarray:
    return np.linalg.norm(np.where(np.isfinite(x), x, 0.0), axis=axis).astype(np.float32)


def build_rollout_features(labels: dict[str, np.ndarray], split: str, valid: np.ndarray) -> np.ndarray:
    pred_z = labels[f"{split}_pred_z"][valid, :MAX_H].astype(np.float32)
    step_valid = labels[f"{split}_valid"][valid, :MAX_H].astype(np.float32)
    pred_z[step_valid < 0.5] = 0.0
    zero = np.zeros((len(pred_z), 1, pred_z.shape[-1]), dtype=np.float32)
    previous = np.concatenate([zero, pred_z[:, :-1]], axis=1)
    delta = (pred_z - previous).astype(np.float32)
    delta[step_valid < 0.5] = 0.0
    delta_norm = safe_norm(delta, axis=2)
    rollout_norm = safe_norm(pred_z, axis=2)
    if len(pred_z) == 0:
        time_features = np.zeros((0, 2), dtype=np.float32)
    else:
        anchors = labels[f"{split}_anchor_ep_t0"][valid].astype(np.float32)
        t0 = anchors[:, 1]
        time_features = np.stack(
            [
                t0 / float(max(1.0, float(np.max(t0)))),
                np.ones_like(t0, dtype=np.float32),
            ],
            axis=1,
        ).astype(np.float32)
    return np.concatenate(
        [
            pred_z.reshape(len(pred_z), -1),
            delta.reshape(len(delta), -1),
            rollout_norm,
            delta_norm,
            step_valid,
            time_features,
        ],
        axis=1,
    ).astype(np.float32)


def split_payload(labels: dict[str, np.ndarray], split: str) -> dict[str, np.ndarray]:
    indices = horizon_indices(labels, DEPTHS)
    valid = labels[f"{split}_valid"][:, indices].all(axis=1)
    anchors = labels[f"{split}_anchor_ep_t0"][valid].astype(np.int64)
    err_at_h = labels[f"{split}_err_at_h"][valid].astype(np.float64)
    option_error = np.zeros((len(anchors), len(DEPTHS)), dtype=np.float64)
    for col, depth in enumerate(DEPTHS):
        option_error[:, col] = np.sum(err_at_h[:, : int(depth)], axis=1)
    mid = int(np.where(DEPTHS == 3)[0][0])
    uniform_error = option_error[:, mid].copy()
    true_mv = uniform_error[:, None] / 3.0 - option_error / DEPTHS[None, :].astype(np.float64)
    return {
        "x": build_rollout_features(labels, split, valid),
        "episode": anchors[:, 0].astype(np.int64),
        "t0": anchors[:, 1].astype(np.int64),
        "anchor_ep_t0": anchors,
        "option_error": option_error,
        "uniform_error": uniform_error,
        "true_mv": true_mv,
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
        "health": health,
        "calibration": health["best"]["calibration"],
        "eval": structured.evaluate_scores(eval_payload, eval_score, seed=seed + 1001),
        "references": {
            "exact_budget_oracle": structured.exact_oracle(eval_payload, seed=seed + 1003),
            "per_step_oracle": structured.per_step_oracle(eval_payload, seed=seed + 1005),
        },
    }
    return report, eval_score, choice


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    learned = report["eval"]["learned_rollout_only"]["allocation_delta"]
    exact = report["eval"]["exact_budget_oracle"]["allocation_delta"]
    lines = [
        "# Compute-Value Independent Rollout-Only",
        "",
        f"- status: `{report['status']}`",
        f"- source: `{report['inputs']['labels']}`",
        f"- device: `{report['device']}`",
        f"- eval anchors: `{report['counts']['eval']}` across `{report['counts']['eval_episodes']}` episodes",
        f"- learned rollout-only delta: `{learned['observed']:.9g}` `[{learned['low']:.9g}, {learned['high']:.9g}]`",
        f"- exact-budget oracle delta: `{exact['observed']:.9g}` `[{exact['low']:.9g}, {exact['high']:.9g}]`",
        "",
        "This is an independent-export rollout-only test. It does not use base latent/action features and is not a full structured-assignment replication.",
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Run independent-export rollout-only structured compute-value assignment")
    parser.add_argument("--labels", default=str(DEFAULT_LABELS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=41)
    parser.add_argument("--epochs", type=int, default=280)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    labels_path = Path(args.labels)
    if not labels_path.exists():
        raise FileNotFoundError(labels_path)
    labels = load_npz(labels_path)
    train = split_payload(labels, "train")
    cal = split_payload(labels, "calibration")
    eval_payload = split_payload(labels, "eval")
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
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
    structured.write_npz(Path(args.out), eval_payload, eval_score, choice, "independent_rollout_only")
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_independent_rollout_only",
        "device": str(device),
        "inputs": {"labels": str(labels_path)},
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
            "feature_scope": "independent export predicted rollout trajectory, rollout deltas, rollout norms, validity, and timing only",
        },
        "calibration": {"learned_rollout_only": row["calibration"]},
        "eval": {
            "learned_rollout_only": row["eval"],
            "exact_budget_oracle": row["references"]["exact_budget_oracle"],
            "per_step_oracle": row["references"]["per_step_oracle"],
        },
        "health": row["health"],
        "leakage_attestation": {
            "features": "built only from split pred_z, valid masks, and anchor timing; err_at_h is used only for labels and evaluation",
            "feature_standardizer": "fit on train rollout-only features",
            "target_standardizer": "fit on train option_error only",
            "model_selection": "calibration split exact-budget allocation only",
            "eval_truth_usage": "eval option_error used only after predicted option scores are produced",
            "not_full_replication": "base latent/action features are absent from the independent export",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"device": str(device), "eval": report["eval"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
