from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import _compute_value_model as cvm
import _compute_value_option_set as optset
import _g2n_integrated_a100 as g2n


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_refined_option_model.json"
DEFAULT_MD = REPORT_DIR / "compute_value_refined_option_model.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_refined_option_model_predictions.npz"
DEPTHS = np.asarray([1, 2, 3, 4, 5], dtype=np.int64)


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


def resolve_path(requested: str, candidates: list[Path]) -> Path:
    return cvm.resolve_path(requested, candidates)


def load_npz(path: Path) -> dict[str, np.ndarray]:
    return cvm.load_npz(path)


def horizon_indices(labels: dict[str, np.ndarray], depths: np.ndarray) -> list[int]:
    horizons = [int(item) for item in labels["horizons"].reshape(-1)]
    return [horizons.index(int(depth)) for depth in depths]


def split_payload(labels: dict[str, np.ndarray], latents: dict[str, np.ndarray], split: str) -> dict[str, np.ndarray]:
    indices = horizon_indices(labels, DEPTHS)
    valid = labels[f"{split}_valid"][:, indices].all(axis=1)
    rows = g2n.build_features(latents, labels, split, use_rollout=True)
    anchors = rows["anchor_ep_t0"][valid].astype(np.int64)
    err_at_h = labels[f"{split}_err_at_h"][valid].astype(np.float64)
    option_error = np.zeros((len(anchors), len(DEPTHS)), dtype=np.float64)
    for col, depth in enumerate(DEPTHS):
        option_error[:, col] = np.sum(err_at_h[:, : int(depth)], axis=1)
    mid = int(np.where(DEPTHS == 3)[0][0])
    uniform_error = option_error[:, mid].copy()
    mv = uniform_error[:, None] / 3.0 - option_error / DEPTHS[None, :].astype(np.float64)
    return {
        "x": rows["x"][valid].astype(np.float32),
        "episode": anchors[:, 0].astype(np.int64),
        "t0": anchors[:, 1].astype(np.int64),
        "anchor_ep_t0": anchors,
        "option_error": option_error,
        "uniform_error": uniform_error,
        "true_mv": mv.astype(np.float64),
        "feature_groups": rows["feature_groups"],
    }


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    return cvm.fit_standardizer(x.astype(np.float32))


def standardize(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return cvm.apply_standardizer(x.astype(np.float32), mean, scale)


def train_ridge(x: np.ndarray, y: np.ndarray, *, alpha: float) -> tuple[np.ndarray, np.ndarray]:
    x_aug = np.concatenate([x, np.ones((len(x), 1), dtype=np.float32)], axis=1).astype(np.float64)
    eye = np.eye(x_aug.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    weights = np.linalg.solve(x_aug.T @ x_aug + alpha * eye, x_aug.T @ y.astype(np.float64))
    return weights[:-1].astype(np.float64), weights[-1].astype(np.float64)


def predict_ridge(x: np.ndarray, w: np.ndarray, b: np.ndarray) -> np.ndarray:
    return (x.astype(np.float64) @ w + b).astype(np.float64)


class RefinedMLP(nn.Module):
    def __init__(self, in_dim: int, hidden: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, hidden),
            nn.SiLU(),
            nn.LayerNorm(hidden),
            nn.Dropout(0.05),
            nn.Linear(hidden, hidden // 2),
            nn.SiLU(),
            nn.LayerNorm(hidden // 2),
            nn.Linear(hidden // 2, len(DEPTHS)),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


def train_mlp(
    x_train: np.ndarray,
    y_train: np.ndarray,
    x_cal: np.ndarray,
    y_cal: np.ndarray,
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    epochs: int,
    batch: int,
    lr: float,
) -> tuple[RefinedMLP, dict[str, Any]]:
    torch.manual_seed(seed + 701)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed + 701)
    model = RefinedMLP(x_train.shape[1], hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_train.astype(np.float32)).to(device)
    x_c = torch.from_numpy(x_cal.astype(np.float32)).to(device)
    y_c = torch.from_numpy(y_cal.astype(np.float32)).to(device)
    rng = np.random.default_rng(seed + 701)
    best_state = None
    best_cal = float("inf")
    history: list[dict[str, float]] = []
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(len(x_train))
        losses = []
        for start in range(0, len(order), batch):
            idx = torch.as_tensor(order[start : start + batch], dtype=torch.long, device=device)
            pred = model(x_t[idx])
            point_loss = F.smooth_l1_loss(pred, y_t[idx])
            # Preserve option ordering as well as point values.
            diff_pred = pred[:, :, None] - pred[:, None, :]
            diff_true = y_t[idx, :, None] - y_t[idx, None, :]
            sign = torch.sign(diff_true)
            mask = torch.abs(diff_true) > 1.0e-6
            rank_loss = F.softplus(-sign[mask] * diff_pred[mask]).mean() if torch.any(mask) else point_loss * 0.0
            loss = point_loss + 0.1 * rank_loss
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        model.eval()
        with torch.inference_mode():
            cal_loss = float(F.smooth_l1_loss(model(x_c), y_c).detach().cpu())
        history.append({"epoch": float(epoch + 1), "train": clean_float(float(np.mean(losses))), "cal": clean_float(cal_loss)})
        if cal_loss < best_cal:
            best_cal = cal_loss
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "best_cal_smooth_l1": clean_float(best_cal),
        "history_first": history[0],
        "history_last": history[-1],
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def predict_mlp(model: RefinedMLP, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros((len(x), len(DEPTHS)), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            out[start : start + batch] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def score_from_mv(predicted_mv: np.ndarray) -> np.ndarray:
    low = int(np.where(DEPTHS < 3)[0][0])
    high = int(np.where(DEPTHS > 3)[0][-1])
    return predicted_mv[:, high] - predicted_mv[:, low]


def evaluate(payload: dict[str, np.ndarray], predicted_mv: np.ndarray, *, seed: int) -> dict[str, Any]:
    score = score_from_mv(predicted_mv)
    chosen = optset.balanced_choice(payload["episode"], score, DEPTHS)
    metrics = optset.evaluate(payload["episode"], payload["option_error"], DEPTHS, chosen, seed=seed)
    target = score_from_mv(payload["true_mv"])
    metrics["score_spearman"] = cvm.spearman(score, target)
    return metrics


def write_npz(path: Path, payload: dict[str, np.ndarray], predicted_mv: np.ndarray, model_name: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        episode=payload["episode"].astype(np.int64),
        t0=payload["t0"].astype(np.int64),
        anchor_ep_t0=payload["anchor_ep_t0"].astype(np.int64),
        option_depths=DEPTHS.astype(np.int64),
        option_error=payload["option_error"].astype(np.float64),
        uniform_error=payload["uniform_error"].astype(np.float64),
        true_mv=payload["true_mv"].astype(np.float64),
        predicted_mv=predicted_mv.astype(np.float64),
        policy_score=score_from_mv(predicted_mv).astype(np.float64),
        model_name=np.asarray(model_name, dtype=np.str_),
    )


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    eval_row = report["eval"]
    delta = eval_row["allocation_delta"]
    oracle = report["references"]["oracle"]["allocation_delta"]
    reused = report["references"]["reused_policy_score"]["allocation_delta"]
    lines = [
        "# Compute-Value Refined Option Model",
        "",
        f"- selected model: `{report['selected_model']}`",
        f"- device: `{report['device']}`",
        f"- eval allocation delta: `{delta['observed']:.9g}` `[{delta['low']:.9g}, {delta['high']:.9g}]`",
        f"- oracle delta: `{oracle['observed']:.9g}` `[{oracle['low']:.9g}, {oracle['high']:.9g}]`",
        f"- reused policy-score delta: `{reused['observed']:.9g}` `[{reused['low']:.9g}, {reused['high']:.9g}]`",
        f"- eval score Spearman: `{eval_row['score_spearman']:.9g}`",
        "",
        "| candidate | calibration delta | calibration rho |",
        "|---|---:|---:|",
    ]
    for name, row in report["calibration"].items():
        d = row["allocation_delta"]
        lines.append(f"| `{name}` | {d['observed']:.9g} [{d['low']:.9g}, {d['high']:.9g}] | {row['score_spearman']:.9g} |")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train refined option-set compute-value readouts")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=29)
    parser.add_argument("--epochs", type=int, default=400)
    parser.add_argument("--hidden", type=int, default=384)
    parser.add_argument("--batch", type=int, default=256)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    labels_path = resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS])
    latents_path = resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS])
    labels = load_npz(labels_path)
    latents = load_npz(latents_path)
    train = split_payload(labels, latents, "train")
    cal = split_payload(labels, latents, "calibration")
    eval_payload = split_payload(labels, latents, "eval")
    x_mean, x_scale = fit_standardizer(train["x"])
    x_train = standardize(train["x"], x_mean, x_scale)
    x_cal = standardize(cal["x"], x_mean, x_scale)
    x_eval = standardize(eval_payload["x"], x_mean, x_scale)
    y_mean, y_scale = fit_standardizer(train["true_mv"].astype(np.float32))
    y_train = standardize(train["true_mv"].astype(np.float32), y_mean, y_scale)
    y_cal = standardize(cal["true_mv"].astype(np.float32), y_mean, y_scale)

    candidates: dict[str, dict[str, Any]] = {}
    cal_pred: dict[str, np.ndarray] = {}
    eval_pred: dict[str, np.ndarray] = {}
    for alpha in (1.0, 10.0, 100.0):
        name = f"ridge_alpha_{alpha:g}"
        w, b = train_ridge(x_train, y_train, alpha=alpha)
        cal_out = predict_ridge(x_cal, w, b) * y_scale + y_mean
        eval_out = predict_ridge(x_eval, w, b) * y_scale + y_mean
        cal_pred[name] = cal_out
        eval_pred[name] = eval_out
        candidates[name] = {"kind": "ridge", "calibration": evaluate(cal, cal_out, seed=int(args.seed) + 101)}

    mlp, health = train_mlp(
        x_train,
        y_train,
        x_cal,
        y_cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    mlp_cal = predict_mlp(mlp, x_cal, device, int(args.batch)) * y_scale + y_mean
    mlp_eval = predict_mlp(mlp, x_eval, device, int(args.batch)) * y_scale + y_mean
    cal_pred["mlp"] = mlp_cal
    eval_pred["mlp"] = mlp_eval
    candidates["mlp"] = {"kind": "mlp", "health": health, "calibration": evaluate(cal, mlp_cal, seed=int(args.seed) + 101)}

    def key(name: str) -> tuple[float, float, str]:
        d = candidates[name]["calibration"]["allocation_delta"]
        return (float(d["high"]), float(d["observed"]), name)

    selected = min(candidates, key=key)
    selected_eval = eval_pred[selected]
    eval_metrics = evaluate(eval_payload, selected_eval, seed=int(args.seed) + 211)
    write_npz(Path(args.out), eval_payload, selected_eval, selected)

    oracle_choice = np.argmin(eval_payload["option_error"] / DEPTHS[None, :].astype(np.float64), axis=1)
    oracle_metrics = optset.evaluate(eval_payload["episode"], eval_payload["option_error"], DEPTHS, oracle_choice, seed=int(args.seed) + 307)
    reused_score = np.load(REPORT_DIR / "compute_value_policy_stability_predictions.npz", allow_pickle=False)["policy_score"].astype(np.float64)
    reused_choice = optset.balanced_choice(eval_payload["episode"], reused_score, DEPTHS)
    reused_metrics = optset.evaluate(eval_payload["episode"], eval_payload["option_error"], DEPTHS, reused_choice, seed=int(args.seed) + 311)
    reused_metrics["score_spearman"] = cvm.spearman(reused_score, score_from_mv(eval_payload["true_mv"]))

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_refined_option_model",
        "selected_model": selected,
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
        },
        "option_depths": DEPTHS.tolist(),
        "calibration": {name: candidates[name]["calibration"] for name in sorted(candidates)},
        "model_details": {name: {k: v for k, v in candidates[name].items() if k != "calibration"} for name in sorted(candidates)},
        "eval": eval_metrics,
        "references": {"oracle": oracle_metrics, "reused_policy_score": reused_metrics},
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only",
            "target_standardizer": "fit on train true_mv only",
            "model_selection": "calibration split only",
            "eval_truth_usage": "eval option_error and true_mv used only after predicted_mv is written for final metrics",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"selected_model": selected, "eval": eval_metrics, "references": report["references"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
