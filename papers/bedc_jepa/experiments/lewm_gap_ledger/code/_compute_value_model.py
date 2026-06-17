from __future__ import annotations

import argparse
import json
import math
import random
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import _g2n_integrated_a100 as g2n


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
ALT_LABELS = Path("C:/OMEGA/le-wm-survey/reports/g2n_labels_clean.npz")
DEFAULT_LATENTS = ROOT / "tworooms_latent_large.npz"
ALT_LATENTS = Path("C:/OMEGA/le-wm-survey/tworooms_latent_large.npz")
DEFAULT_OUT = REPORT_DIR / "compute_value_model_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "compute_value_model.json"
DEFAULT_MD = REPORT_DIR / "compute_value_model.md"

OPTION_DEPTHS = np.asarray([1, 3, 5], dtype=np.int64)
UNIFORM_DEPTH = 3
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


def resolve_path(requested: str, candidates: list[Path]) -> Path:
    paths = [Path(requested), *candidates]
    for path in paths:
        if path.exists():
            return path
    raise FileNotFoundError("missing artifact; checked " + ", ".join(str(path) for path in paths))


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def horizon_index(labels: dict[str, np.ndarray], h: int) -> int:
    horizons = [int(item) for item in labels["horizons"].reshape(-1)]
    if h not in horizons:
        raise RuntimeError(f"missing horizon {h}")
    return int(horizons.index(h))


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def split_payload(
    labels: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
    split: str,
) -> dict[str, np.ndarray]:
    h5_idx = horizon_index(labels, 5)
    valid = labels[f"{split}_valid"][:, h5_idx].astype(bool)
    rows = g2n.build_features(latents, labels, split, use_rollout=True)
    anchors = rows["anchor_ep_t0"][valid].astype(np.int64)
    err_at_h = labels[f"{split}_err_at_h"][valid].astype(np.float64)
    option_error = np.zeros((len(anchors), len(OPTION_DEPTHS)), dtype=np.float64)
    for col, h in enumerate(OPTION_DEPTHS):
        option_error[:, col] = np.sum(err_at_h[:, : int(h)], axis=1)
    uniform_col = int(np.where(OPTION_DEPTHS == UNIFORM_DEPTH)[0][0])
    uniform_error = option_error[:, uniform_col].copy()
    true_mv = uniform_error[:, None] / float(UNIFORM_DEPTH) - option_error / OPTION_DEPTHS[None, :]
    return {
        "x": rows["x"][valid].astype(np.float32),
        "episode": anchors[:, 0].astype(np.int64),
        "t0": anchors[:, 1].astype(np.int64),
        "anchor_ep_t0": anchors,
        "option_error": option_error.astype(np.float64),
        "uniform_error": uniform_error.astype(np.float64),
        "true_mv": true_mv.astype(np.float64),
        "option_steps": OPTION_DEPTHS.astype(np.float64),
        "uniform_steps": np.full(len(anchors), UNIFORM_DEPTH, dtype=np.float64),
    }


def rankdata(values: np.ndarray) -> np.ndarray:
    order = np.argsort(values, kind="mergesort")
    ranks = np.empty(len(values), dtype=np.float64)
    sorted_values = values[order]
    i = 0
    while i < len(values):
        j = i + 1
        while j < len(values) and sorted_values[j] == sorted_values[i]:
            j += 1
        ranks[order[i:j]] = 0.5 * (i + j - 1)
        i = j
    return ranks


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    if len(x) < 2:
        return 0.0
    rx = rankdata(np.asarray(x, dtype=np.float64))
    ry = rankdata(np.asarray(y, dtype=np.float64))
    rx = rx - float(rx.mean())
    ry = ry - float(ry.mean())
    denom = math.sqrt(float(np.dot(rx, rx)) * float(np.dot(ry, ry)))
    if denom <= 0.0:
        return 0.0
    return clean_float(float(np.dot(rx, ry) / denom))


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0] for ep in np.unique(episode)]


def balanced_depth_choice(episode: np.ndarray, predicted_mv: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    low = int(np.where(OPTION_DEPTHS < UNIFORM_DEPTH)[0][0])
    mid = int(np.where(OPTION_DEPTHS == UNIFORM_DEPTH)[0][0])
    high = int(np.where(OPTION_DEPTHS > UNIFORM_DEPTH)[0][-1])
    score = predicted_mv[:, high] - predicted_mv[:, low]
    chosen = np.full(len(episode), mid, dtype=np.int64)
    for idxs in episode_groups(episode):
        ordered = sorted((int(i) for i in idxs), key=lambda i: (float(score[i]), int(i)))
        n = len(ordered)
        half = n // 2
        chosen[np.asarray(ordered[:half], dtype=np.int64)] = low
        chosen[np.asarray(ordered[n - half :], dtype=np.int64)] = high
        if n % 2:
            chosen[ordered[half]] = mid
        steps = OPTION_DEPTHS[chosen[np.asarray(ordered, dtype=np.int64)]]
        if int(np.sum(steps)) != UNIFORM_DEPTH * n:
            raise RuntimeError("balanced compute-value allocation budget mismatch")
    return chosen, score


def evaluate_prediction(payload: dict[str, np.ndarray], predicted_mv: np.ndarray, *, seed: int) -> dict[str, Any]:
    episode = payload["episode"].astype(np.int64)
    option_error = payload["option_error"].astype(np.float64)
    uniform_error = payload["uniform_error"].astype(np.float64)
    true_mv = payload["true_mv"].astype(np.float64)
    chosen, rank_score = balanced_depth_choice(episode, predicted_mv.astype(np.float64))
    chosen_error = option_error[np.arange(len(chosen)), chosen]
    chosen_steps = OPTION_DEPTHS[chosen].astype(np.float64)
    uniform_steps = np.full(len(chosen), UNIFORM_DEPTH, dtype=np.float64)

    groups = episode_groups(episode)
    selected_ep_error = np.asarray([float(np.sum(chosen_error[idx])) for idx in groups], dtype=np.float64)
    selected_ep_steps = np.asarray([float(np.sum(chosen_steps[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_error = np.asarray([float(np.sum(uniform_error[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_steps = np.asarray([float(np.sum(uniform_steps[idx])) for idx in groups], dtype=np.float64)
    observed = clean_float(float(selected_ep_error.sum() / selected_ep_steps.sum() - uniform_ep_error.sum() / uniform_ep_steps.sum()))
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(groups), size=len(groups))
        samples[i] = float(
            selected_ep_error[pick].sum() / selected_ep_steps[pick].sum()
            - uniform_ep_error[pick].sum() / uniform_ep_steps[pick].sum()
        )
    low_idx = int(np.where(OPTION_DEPTHS < UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(OPTION_DEPTHS > UNIFORM_DEPTH)[0][-1])
    true_rank_score = true_mv[:, high_idx] - true_mv[:, low_idx]
    return {
        "allocation_delta": {
            "observed": observed,
            "low": clean_float(float(np.percentile(samples, 2.5))),
            "high": clean_float(float(np.percentile(samples, 97.5))),
        },
        "mv_spearman": spearman(rank_score, true_rank_score),
        "chosen_depth_counts": {str(int(k)): int(v) for k, v in zip(*np.unique(OPTION_DEPTHS[chosen], return_counts=True))},
    }


class ComputeValueMLP(nn.Module):
    def __init__(self, in_dim: int, hidden: int, out_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, hidden),
            nn.SiLU(),
            nn.LayerNorm(hidden),
            nn.Dropout(0.05),
            nn.Linear(hidden, hidden // 2),
            nn.SiLU(),
            nn.LayerNorm(hidden // 2),
            nn.Linear(hidden // 2, out_dim),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class ScalarRankNet(nn.Module):
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
            nn.Linear(hidden // 2, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def train_ridge(x: np.ndarray, y: np.ndarray, *, alpha: float) -> tuple[np.ndarray, np.ndarray]:
    x_aug = np.concatenate([x, np.ones((len(x), 1), dtype=np.float32)], axis=1).astype(np.float64)
    eye = np.eye(x_aug.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    weights = np.linalg.solve(x_aug.T @ x_aug + alpha * eye, x_aug.T @ y.astype(np.float64))
    return weights[:-1].astype(np.float64), weights[-1].astype(np.float64)


def predict_ridge(x: np.ndarray, w: np.ndarray, b: np.ndarray) -> np.ndarray:
    return (x.astype(np.float64) @ w + b).astype(np.float64)


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
) -> tuple[ComputeValueMLP, dict[str, Any]]:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = ComputeValueMLP(x_train.shape[1], hidden, y_train.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_train.astype(np.float32)).to(device)
    x_c = torch.from_numpy(x_cal.astype(np.float32)).to(device)
    y_c = torch.from_numpy(y_cal.astype(np.float32)).to(device)
    rng = np.random.default_rng(seed)
    best_state = None
    best_cal = float("inf")
    history: list[dict[str, float]] = []
    low_idx = int(np.where(OPTION_DEPTHS < UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(OPTION_DEPTHS > UNIFORM_DEPTH)[0][-1])
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(len(x_train))
        losses: list[float] = []
        for lo in range(0, len(order), batch):
            idx = torch.from_numpy(order[lo : lo + batch]).to(device)
            pred = model(x_t[idx])
            target = y_t[idx]
            mse = F.mse_loss(pred, target)
            pred_diff = pred[:, high_idx] - pred[:, low_idx]
            true_diff = target[:, high_idx] - target[:, low_idx]
            rank_mse = F.mse_loss(pred_diff, true_diff)
            loss = mse + 0.5 * rank_mse
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        model.eval()
        with torch.inference_mode():
            cal_pred = model(x_c)
            cal_loss = float(F.mse_loss(cal_pred, y_c).detach().cpu())
        train_loss = float(np.mean(losses)) if losses else float("inf")
        history.append({"epoch": float(epoch + 1), "train": train_loss, "cal": cal_loss})
        if cal_loss < best_cal:
            best_cal = cal_loss
            best_state = {key: value.detach().cpu().clone() for key, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    model.eval()
    return model, {
        "best_cal_mse": clean_float(best_cal),
        "loss_first": history[0] if history else {},
        "loss_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def train_ranknet(
    x_train: np.ndarray,
    target_train: np.ndarray,
    episode_train: np.ndarray,
    x_cal: np.ndarray,
    target_cal: np.ndarray,
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    epochs: int,
    batch: int,
    lr: float,
) -> tuple[ScalarRankNet, dict[str, Any]]:
    torch.manual_seed(seed + 1009)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed + 1009)
    model = ScalarRankNet(x_train.shape[1], hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(target_train.astype(np.float32)).to(device)
    x_c = torch.from_numpy(x_cal.astype(np.float32)).to(device)
    y_c = torch.from_numpy(target_cal.astype(np.float32)).to(device)
    groups = [idx.astype(np.int64) for idx in episode_groups(episode_train.astype(np.int64)) if len(idx) >= 2]
    rng = np.random.default_rng(seed + 1009)
    best_state = None
    best_cal = float("inf")
    history: list[dict[str, float]] = []
    for epoch in range(epochs):
        model.train()
        losses: list[float] = []
        steps = max(1, math.ceil(len(x_train) / batch))
        for _ in range(steps):
            pair_i: list[int] = []
            pair_j: list[int] = []
            while len(pair_i) < batch:
                group = groups[int(rng.integers(0, len(groups)))]
                a, b = rng.choice(group, size=2, replace=False)
                if target_train[int(a)] == target_train[int(b)]:
                    continue
                pair_i.append(int(a))
                pair_j.append(int(b))
            i_t = torch.as_tensor(pair_i, dtype=torch.long, device=device)
            j_t = torch.as_tensor(pair_j, dtype=torch.long, device=device)
            score_i = model(x_t[i_t])
            score_j = model(x_t[j_t])
            sign = torch.sign(y_t[i_t] - y_t[j_t])
            rank_loss = F.softplus(-sign * (score_i - score_j)).mean()
            point_idx = torch.unique(torch.cat([i_t, j_t]))
            point_loss = F.mse_loss(model(x_t[point_idx]), y_t[point_idx])
            loss = rank_loss + 0.1 * point_loss
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        model.eval()
        with torch.inference_mode():
            cal_score = model(x_c)
            cal_loss = float(F.mse_loss(cal_score, y_c).detach().cpu())
        train_loss = float(np.mean(losses)) if losses else float("inf")
        history.append({"epoch": float(epoch + 1), "train": train_loss, "cal": cal_loss})
        if cal_loss < best_cal:
            best_cal = cal_loss
            best_state = {key: value.detach().cpu().clone() for key, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    model.eval()
    return model, {
        "best_cal_score_mse": clean_float(best_cal),
        "loss_first": history[0] if history else {},
        "loss_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def predict_mlp(model: ComputeValueMLP, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros((len(x), 3), dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, len(x), batch):
            hi = min(lo + batch, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            out[lo:hi] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def predict_ranknet(model: ScalarRankNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    score = np.zeros(len(x), dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, len(x), batch):
            hi = min(lo + batch, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            score[lo:hi] = model(xb).detach().cpu().numpy().astype(np.float64)
    predicted_mv = np.zeros((len(x), len(OPTION_DEPTHS)), dtype=np.float64)
    low_idx = int(np.where(OPTION_DEPTHS < UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(OPTION_DEPTHS > UNIFORM_DEPTH)[0][-1])
    predicted_mv[:, low_idx] = 0.0
    predicted_mv[:, high_idx] = score
    return predicted_mv


def write_prediction_npz(path: Path, payload: dict[str, np.ndarray], predicted_mv: np.ndarray, model_name: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        episode=payload["episode"].astype(np.int64),
        t0=payload["t0"].astype(np.int64),
        anchor_ep_t0=payload["anchor_ep_t0"].astype(np.int64),
        option_depths=OPTION_DEPTHS.astype(np.int64),
        option_steps=OPTION_DEPTHS.astype(np.float64),
        uniform_steps=payload["uniform_steps"].astype(np.float64),
        option_error=payload["option_error"].astype(np.float64),
        uniform_error=payload["uniform_error"].astype(np.float64),
        true_mv=payload["true_mv"].astype(np.float64),
        predicted_mv=predicted_mv.astype(np.float64),
        model_name=np.asarray(model_name, dtype=np.str_),
    )


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    selected = report["selected_model"]
    eval_delta = report["eval"]["allocation_delta"]
    lines = [
        "# Compute-Value Model",
        "",
        f"- selected model: `{selected}`",
        f"- device: `{report['device']}`",
        f"- eval allocation delta: `{eval_delta['observed']:.9g}` `[{eval_delta['low']:.9g}, {eval_delta['high']:.9g}]`",
        f"- eval MV Spearman: `{report['eval']['mv_spearman']:.9g}`",
        "",
        "| model | calibration delta | calibration rho |",
        "|---|---:|---:|",
    ]
    for name, row in report["calibration"].items():
        d = row["allocation_delta"]
        lines.append(f"| `{name}` | {d['observed']:.9g} [{d['low']:.9g}, {d['high']:.9g}] | {row['mv_spearman']:.9g} |")
    lines.extend(
        [
            "",
            "The selected prediction artifact contains model outputs in `predicted_mv`; eval option errors are used only by the final gate.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train local BEDC-JEPA compute-value predictors")
    parser.add_argument("--labels", default=str(DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(DEFAULT_LATENTS))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--epochs", type=int, default=700)
    parser.add_argument("--batch", type=int, default=256)
    parser.add_argument("--hidden", type=int, default=512)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    random.seed(int(args.seed))
    np.random.seed(int(args.seed))
    torch.manual_seed(int(args.seed))
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(int(args.seed))
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    labels_path = resolve_path(str(args.labels), [DEFAULT_LABELS, ALT_LABELS])
    latents_path = resolve_path(str(args.latents), [DEFAULT_LATENTS, ALT_LATENTS])
    labels = load_npz(labels_path)
    latents = load_npz(latents_path)
    train = split_payload(labels, latents, "train")
    cal = split_payload(labels, latents, "calibration")
    eval_payload = split_payload(labels, latents, "eval")

    x_mean, x_scale = fit_standardizer(train["x"])
    y_mean, y_scale = fit_standardizer(train["true_mv"].astype(np.float32))
    x_train = apply_standardizer(train["x"], x_mean, x_scale)
    x_cal = apply_standardizer(cal["x"], x_mean, x_scale)
    x_eval = apply_standardizer(eval_payload["x"], x_mean, x_scale)
    y_train = apply_standardizer(train["true_mv"].astype(np.float32), y_mean, y_scale)
    y_cal = apply_standardizer(cal["true_mv"].astype(np.float32), y_mean, y_scale)

    candidates: dict[str, dict[str, Any]] = {}
    predictions_cal: dict[str, np.ndarray] = {}
    predictions_eval: dict[str, np.ndarray] = {}

    for alpha in (1.0, 10.0, 100.0):
        name = f"ridge_alpha_{alpha:g}"
        w, b = train_ridge(x_train, y_train, alpha=alpha)
        cal_pred = predict_ridge(x_cal, w, b) * y_scale + y_mean
        eval_pred = predict_ridge(x_eval, w, b) * y_scale + y_mean
        predictions_cal[name] = cal_pred
        predictions_eval[name] = eval_pred
        candidates[name] = {
            "kind": "ridge",
            "alpha": alpha,
            "calibration": evaluate_prediction(cal, cal_pred, seed=int(args.seed) + 11),
        }

    mlp, mlp_health = train_mlp(
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
    mlp_cal_pred = predict_mlp(mlp, x_cal, device, int(args.batch)) * y_scale + y_mean
    mlp_eval_pred = predict_mlp(mlp, x_eval, device, int(args.batch)) * y_scale + y_mean
    predictions_cal["mlp"] = mlp_cal_pred
    predictions_eval["mlp"] = mlp_eval_pred
    candidates["mlp"] = {
        "kind": "mlp",
        "health": mlp_health,
        "calibration": evaluate_prediction(cal, mlp_cal_pred, seed=int(args.seed) + 11),
    }

    low_idx = int(np.where(OPTION_DEPTHS < UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(OPTION_DEPTHS > UNIFORM_DEPTH)[0][-1])
    rank_target_train = (train["true_mv"][:, high_idx] - train["true_mv"][:, low_idx]).astype(np.float32)
    rank_target_cal = (cal["true_mv"][:, high_idx] - cal["true_mv"][:, low_idx]).astype(np.float32)
    rt_mean = float(np.mean(rank_target_train))
    rt_scale = float(np.std(rank_target_train))
    if rt_scale < 1.0e-6:
        rt_scale = 1.0
    rank_model, rank_health = train_ranknet(
        x_train,
        ((rank_target_train - rt_mean) / rt_scale).astype(np.float32),
        train["episode"].astype(np.int64),
        x_cal,
        ((rank_target_cal - rt_mean) / rt_scale).astype(np.float32),
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    rank_cal_pred = predict_ranknet(rank_model, x_cal, device, int(args.batch))
    rank_eval_pred = predict_ranknet(rank_model, x_eval, device, int(args.batch))
    rank_cal_pred *= rt_scale
    rank_eval_pred *= rt_scale
    rank_cal_pred[:, high_idx] += rt_mean
    rank_eval_pred[:, high_idx] += rt_mean
    predictions_cal["ranknet_scalar"] = rank_cal_pred
    predictions_eval["ranknet_scalar"] = rank_eval_pred
    candidates["ranknet_scalar"] = {
        "kind": "ranknet_scalar",
        "health": rank_health,
        "calibration": evaluate_prediction(cal, rank_cal_pred, seed=int(args.seed) + 11),
    }

    def selection_key(name: str) -> tuple[float, float, str]:
        delta = candidates[name]["calibration"]["allocation_delta"]
        return (float(delta["high"]), float(delta["observed"]), name)

    selected = min(candidates, key=selection_key)
    selected_eval_pred = predictions_eval[selected]
    eval_metrics = evaluate_prediction(eval_payload, selected_eval_pred, seed=int(args.seed) + 23)
    out_path = Path(args.out)
    write_prediction_npz(out_path, eval_payload, selected_eval_pred, selected)

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_model",
        "selected_model": selected,
        "selection_rule": "minimize calibration allocation_delta CI high, then observed delta",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
        },
        "feature_groups": [str(item) for item in g2n.build_features(latents, labels, "train", use_rollout=True)["feature_groups"].tolist()],
        "target": {
            "option_depths": OPTION_DEPTHS.tolist(),
            "uniform_depth": UNIFORM_DEPTH,
            "mv": "uniform per-step error - option per-step error",
        },
        "calibration": {name: candidates[name]["calibration"] for name in sorted(candidates)},
        "model_details": {name: {k: v for k, v in candidates[name].items() if k != "calibration"} for name in sorted(candidates)},
        "eval": eval_metrics,
        "outputs": {"predictions_npz": str(out_path), "json": str(args.json), "md": str(args.md)},
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only",
            "target_standardizer": "fit on train true_mv only",
            "model_selection": "calibration split only",
            "eval_truth_usage": "eval option_error and true_mv used only after predicted_mv is written for final metrics",
            "predicted_mv": "model output, not copied from eval true_mv",
        },
        "wall_time_sec": clean_float(time.time() - start),
    }
    json_path = Path(args.json)
    md_path = Path(args.md)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(md_path, report)
    print(json.dumps(clean_json({"selected_model": selected, "eval": eval_metrics, "device": str(device)}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
