from __future__ import annotations

import argparse
import json
import math
import os
import random
import time
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_LATENTS = ROOT / "tworooms_latent_large.npz"
ALT_LATENTS = Path("C:/OMEGA/le-wm-survey/tworooms_latent_large.npz")
DEFAULT_JSON = REPORT_DIR / "native_parity_candidate.json"
DEFAULT_MD = REPORT_DIR / "native_parity_candidate.md"
DEFAULT_OUT = REPORT_DIR / "native_parity_candidate_predictions.npz"
WINDOW_BACK = 4
ACTION_H = 10
BOOTSTRAPS = 500


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


def resolve_path(path: str) -> Path:
    requested = Path(path)
    for candidate in [requested, DEFAULT_LATENTS, ALT_LATENTS]:
        if candidate.exists():
            return candidate
    raise FileNotFoundError(path)


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def split_episodes(n_episodes: int, seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    perm = rng.permutation(n_episodes)
    n_train = int(round(0.60 * n_episodes))
    n_cal = int(round(0.20 * n_episodes))
    return {
        "train": np.sort(perm[:n_train]),
        "calibration": np.sort(perm[n_train : n_train + n_cal]),
        "eval": np.sort(perm[n_train + n_cal :]),
    }


def standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def build_rows(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    emb = data["emb"].astype(np.float32)
    action = data["action"].astype(np.float32)
    pred = data["pred"].astype(np.float32)
    transition_mask = data["transition_mask"].astype(bool)
    lewm_mse = data["prediction_mse"].astype(np.float64)
    selected_len = data.get("selected_ep_len")
    ep_len = selected_len.astype(np.int64) if selected_len is not None else np.full(emb.shape[0], emb.shape[1], dtype=np.int64)
    ep_idx, t_idx = np.where(transition_mask)
    n = len(ep_idx)
    z_dim = int(emb.shape[-1])
    a_dim = int(action.shape[-1])
    z_window = np.zeros((n, WINDOW_BACK + 1, z_dim), dtype=np.float32)
    a_future = np.zeros((n, ACTION_H, a_dim), dtype=np.float32)
    a_valid = np.zeros((n, ACTION_H), dtype=np.float32)
    gap_hist = np.zeros((n, ACTION_H), dtype=np.float32)
    t_features = np.zeros((n, 2), dtype=np.float32)
    current = np.zeros((n, z_dim), dtype=np.float32)
    target = np.zeros((n, z_dim), dtype=np.float32)
    for i, (ep_raw, t_raw) in enumerate(zip(ep_idx, t_idx)):
        ep = int(ep_raw)
        t = int(t_raw)
        limit = int(min(max(ep_len[ep], 1), emb.shape[1]))
        current_t = min(max(t, 0), limit - 2)
        current[i] = emb[ep, current_t]
        target[i] = emb[ep, current_t + 1]
        t_features[i, 0] = float(current_t) / float(max(1, limit - 1))
        t_features[i, 1] = float(limit) / float(max(1, emb.shape[1]))
        for w in range(WINDOW_BACK + 1):
            src = min(max(0, current_t - WINDOW_BACK + w), limit - 1)
            z_window[i, w] = emb[ep, src]
        for h in range(ACTION_H):
            src = current_t + h
            if src < action.shape[1] and src < limit:
                a_future[i, h] = action[ep, src]
                a_valid[i, h] = 1.0
            hist = current_t - ACTION_H + h
            if hist >= 0 and hist < pred.shape[1] and hist + 1 < limit:
                gap_hist[i, h] = float(np.mean((pred[ep, hist] - emb[ep, hist + 1]) ** 2))
    x = np.concatenate(
        [
            z_window.reshape(n, -1),
            a_future.reshape(n, -1),
            a_valid,
            gap_hist,
            t_features,
        ],
        axis=1,
    ).astype(np.float32)
    finite = np.isfinite(x).all(axis=1) & np.isfinite(target).all(axis=1) & np.isfinite(lewm_mse[ep_idx, t_idx])
    return {
        "x": x[finite],
        "current": current[finite],
        "target": target[finite],
        "episode": ep_idx[finite].astype(np.int64),
        "t": t_idx[finite].astype(np.int64),
        "lewm_mse": lewm_mse[ep_idx[finite], t_idx[finite]].astype(np.float64),
    }


class ResidualPredictor(nn.Module):
    def __init__(self, in_dim: int, latent_dim: int, width: int, depth: int) -> None:
        super().__init__()
        blocks: list[nn.Module] = []
        dim = in_dim
        for _ in range(depth):
            blocks.extend([nn.Linear(dim, width), nn.SiLU(), nn.LayerNorm(width), nn.Dropout(0.03)])
            dim = width
        blocks.append(nn.Linear(dim, latent_dim))
        self.net = nn.Sequential(*blocks)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


def configure(seed: int) -> torch.device:
    os.environ["PYTHONHASHSEED"] = str(seed)
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")


def mse(pred: np.ndarray, target: np.ndarray) -> np.ndarray:
    return np.mean((pred.astype(np.float64) - target.astype(np.float64)) ** 2, axis=1)


def bootstrap_mean(values: np.ndarray, episode: np.ndarray, seed: int) -> dict[str, float]:
    observed = clean_float(float(np.mean(values)))
    unique = np.unique(episode)
    groups = [np.where(episode == ep)[0] for ep in unique]
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(groups), size=len(groups))
        idx = np.concatenate([groups[j] for j in pick])
        samples[i] = float(np.mean(values[idx]))
    return {
        "observed": observed,
        "low": clean_float(float(np.percentile(samples, 2.5))),
        "high": clean_float(float(np.percentile(samples, 97.5))),
    }


def predict(model: ResidualPredictor, x: np.ndarray, current: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros_like(current, dtype=np.float32)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            delta = model(xb).detach().cpu().numpy().astype(np.float32)
            out[start : start + batch] = current[start : start + batch] + delta
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a stronger native next-latent parity candidate")
    parser.add_argument("--latents", default=str(DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=73)
    parser.add_argument("--epochs", type=int, default=260)
    parser.add_argument("--width", type=int, default=768)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    parser.add_argument("--epsilon", type=float, default=0.10)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    latents_path = resolve_path(str(args.latents))
    rows = build_rows(load_npz(latents_path))
    splits = split_episodes(int(np.max(rows["episode"])) + 1, int(args.seed))
    masks = {name: np.isin(rows["episode"], eps) for name, eps in splits.items()}
    train = masks["train"]
    cal = masks["calibration"]
    eval_mask = masks["eval"]
    x_mean, x_scale = standardizer(rows["x"][train])
    x_train = apply_standardizer(rows["x"][train], x_mean, x_scale)
    x_cal = apply_standardizer(rows["x"][cal], x_mean, x_scale)
    x_eval = apply_standardizer(rows["x"][eval_mask], x_mean, x_scale)
    delta_train = (rows["target"][train] - rows["current"][train]).astype(np.float32)
    delta_mean, delta_scale = standardizer(delta_train)
    y_train = apply_standardizer(delta_train, delta_mean, delta_scale)
    model = ResidualPredictor(x_train.shape[1], rows["target"].shape[1], int(args.width), int(args.depth)).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=float(args.lr), weight_decay=1.0e-4)
    x_t = torch.from_numpy(x_train).to(device)
    y_t = torch.from_numpy(y_train).to(device)
    x_c = torch.from_numpy(x_cal).to(device)
    cal_target = rows["target"][cal]
    cal_current = rows["current"][cal]
    rng = np.random.default_rng(int(args.seed) + 900)
    best_state = None
    best_cal = float("inf")
    history: list[dict[str, float]] = []
    for epoch in range(int(args.epochs)):
        model.train()
        order = rng.permutation(len(x_train))
        losses: list[float] = []
        for start in range(0, len(order), int(args.batch)):
            idx = torch.as_tensor(order[start : start + int(args.batch)], dtype=torch.long, device=device)
            pred = model(x_t[idx])
            loss = F.smooth_l1_loss(pred, y_t[idx])
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_pred_next = predict(model, x_c.cpu().numpy(), cal_current, device, int(args.batch))
        cal_mse = float(np.mean(mse(cal_pred_next, cal_target)))
        history.append({"epoch": float(epoch + 1), "train": clean_float(float(np.mean(losses))), "cal_mse": clean_float(cal_mse)})
        if cal_mse < best_cal:
            best_cal = cal_mse
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    eval_pred = predict(model, x_eval, rows["current"][eval_mask], device, int(args.batch))
    eval_target = rows["target"][eval_mask]
    eval_episode = rows["episode"][eval_mask]
    native_mse = mse(eval_pred, eval_target)
    lewm_mse = rows["lewm_mse"][eval_mask]
    trivial_mse = mse(rows["current"][eval_mask], eval_target)
    parity_threshold = (1.0 + float(args.epsilon)) * float(np.mean(lewm_mse))
    parity_margin = parity_threshold - float(np.mean(native_mse))
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.native_parity_candidate",
        "device": str(device),
        "inputs": {"latents": str(latents_path)},
        "config": {
            "epochs": int(args.epochs),
            "width": int(args.width),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "epsilon": float(args.epsilon),
            "features": "latent window t-4:t, future action window, action validity, past LeWM gap proxy, time features",
        },
        "counts": {
            "train": int(np.sum(train)),
            "calibration": int(np.sum(cal)),
            "eval": int(np.sum(eval_mask)),
            "eval_episodes": int(len(np.unique(eval_episode))),
            "input_dim": int(rows["x"].shape[1]),
            "params": int(sum(p.numel() for p in model.parameters())),
        },
        "metrics": {
            "native_mse": bootstrap_mean(native_mse, eval_episode, int(args.seed) + 1001),
            "lewm_mse": bootstrap_mean(lewm_mse, eval_episode, int(args.seed) + 1003),
            "trivial_mse": bootstrap_mean(trivial_mse, eval_episode, int(args.seed) + 1005),
            "native_minus_lewm": bootstrap_mean(native_mse - lewm_mse, eval_episode, int(args.seed) + 1007),
            "native_minus_trivial": bootstrap_mean(native_mse - trivial_mse, eval_episode, int(args.seed) + 1009),
        },
        "parity_gate": {
            "threshold": clean_float(parity_threshold),
            "margin": clean_float(parity_margin),
            "pass": bool(parity_margin >= 0.0),
            "native_to_lewm_ratio": clean_float(float(np.mean(native_mse)) / max(float(np.mean(lewm_mse)), 1.0e-12)),
        },
        "health": {
            "best_cal_mse": clean_float(best_cal),
            "history_first": history[0] if history else {},
            "history_last": history[-1] if history else {},
        },
        "leakage_attestation": {
            "standardizers": "fit on train split only",
            "selection": "best epoch selected by calibration next-latent MSE",
            "eval_truth_usage": "eval target latent used only after model selection",
            "lewm_reference": "exported pred-vs-emb next-latent MSE on the same eval transitions",
        },
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    lines = [
        "# Native Parity Candidate",
        "",
        f"- device: `{report['device']}`",
        f"- eval transitions: `{report['counts']['eval']}` across `{report['counts']['eval_episodes']}` episodes",
        f"- native MSE: `{report['metrics']['native_mse']['observed']:.9g}`",
        f"- LeWM MSE: `{report['metrics']['lewm_mse']['observed']:.9g}`",
        f"- trivial MSE: `{report['metrics']['trivial_mse']['observed']:.9g}`",
        f"- native/LeWM ratio: `{report['parity_gate']['native_to_lewm_ratio']:.9g}`",
        f"- parity pass: `{report['parity_gate']['pass']}`",
    ]
    Path(args.md).write_text("\n".join(lines) + "\n", encoding="utf-8")
    np.savez_compressed(
        Path(args.out),
        episode=eval_episode.astype(np.int64),
        t=rows["t"][eval_mask].astype(np.int64),
        pred=eval_pred.astype(np.float32),
        target=eval_target.astype(np.float32),
        native_mse=native_mse.astype(np.float64),
        lewm_mse=lewm_mse.astype(np.float64),
        trivial_mse=trivial_mse.astype(np.float64),
    )
    print(json.dumps(clean_json({"metrics": report["metrics"], "parity_gate": report["parity_gate"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
