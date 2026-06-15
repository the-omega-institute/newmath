from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

from _native_parity_candidate import (
    ACTION_H,
    WINDOW_BACK,
    apply_standardizer,
    bootstrap_mean,
    clean_float,
    clean_json,
    configure,
    load_npz,
    mse,
    resolve_path,
    split_episodes,
    standardizer,
)


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "sequence_native_parity.json"
DEFAULT_MD = REPORT_DIR / "sequence_native_parity.md"
DEFAULT_OUT = REPORT_DIR / "sequence_native_parity_predictions.npz"


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
    z_seq = np.zeros((n, WINDOW_BACK + 1, z_dim), dtype=np.float32)
    a_seq = np.zeros((n, ACTION_H, a_dim + 2), dtype=np.float32)
    gap_hist = np.zeros((n, ACTION_H, 1), dtype=np.float32)
    current = np.zeros((n, z_dim), dtype=np.float32)
    target = np.zeros((n, z_dim), dtype=np.float32)
    t_features = np.zeros((n, 2), dtype=np.float32)
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
            z_seq[i, w] = emb[ep, src]
        for h in range(ACTION_H):
            src = current_t + h
            if src < action.shape[1] and src < limit:
                a_seq[i, h, :a_dim] = action[ep, src]
                a_seq[i, h, a_dim] = 1.0
            a_seq[i, h, a_dim + 1] = float(h) / float(max(1, ACTION_H - 1))
            hist = current_t - ACTION_H + h
            if hist >= 0 and hist < pred.shape[1] and hist + 1 < limit:
                gap_hist[i, h, 0] = float(np.mean((pred[ep, hist] - emb[ep, hist + 1]) ** 2))
    finite = (
        np.isfinite(z_seq).all(axis=(1, 2))
        & np.isfinite(a_seq).all(axis=(1, 2))
        & np.isfinite(gap_hist).all(axis=(1, 2))
        & np.isfinite(target).all(axis=1)
        & np.isfinite(lewm_mse[ep_idx, t_idx])
    )
    return {
        "z_seq": z_seq[finite],
        "a_seq": a_seq[finite],
        "gap_hist": gap_hist[finite],
        "t_features": t_features[finite],
        "current": current[finite],
        "target": target[finite],
        "episode": ep_idx[finite].astype(np.int64),
        "t": t_idx[finite].astype(np.int64),
        "lewm_mse": lewm_mse[ep_idx[finite], t_idx[finite]].astype(np.float64),
    }


class SequencePredictor(nn.Module):
    def __init__(self, z_dim: int, a_dim: int, width: int, depth: int) -> None:
        super().__init__()
        self.z_proj = nn.Linear(z_dim, width)
        self.a_proj = nn.Linear(a_dim, width)
        self.gap_proj = nn.Linear(1, width)
        self.z_gru = nn.GRU(width, width, num_layers=depth, batch_first=True, dropout=0.03 if depth > 1 else 0.0)
        self.a_gru = nn.GRU(width, width, num_layers=depth, batch_first=True, dropout=0.03 if depth > 1 else 0.0)
        self.g_gru = nn.GRU(width, width, num_layers=1, batch_first=True)
        self.head = nn.Sequential(
            nn.LayerNorm(width * 3 + 2),
            nn.Linear(width * 3 + 2, width),
            nn.SiLU(),
            nn.LayerNorm(width),
            nn.Linear(width, z_dim),
        )

    def forward(self, z_seq: torch.Tensor, a_seq: torch.Tensor, gap_hist: torch.Tensor, t_features: torch.Tensor) -> torch.Tensor:
        _, z_h = self.z_gru(F.silu(self.z_proj(z_seq)))
        _, a_h = self.a_gru(F.silu(self.a_proj(a_seq)))
        _, g_h = self.g_gru(F.silu(self.gap_proj(gap_hist)))
        h = torch.cat([z_h[-1], a_h[-1], g_h[-1], t_features], dim=1)
        return self.head(h)


def scale_rows(rows: dict[str, np.ndarray], train: np.ndarray) -> dict[str, np.ndarray]:
    out = dict(rows)
    z_mean, z_scale = standardizer(rows["z_seq"][train].reshape(-1, rows["z_seq"].shape[-1]))
    a_mean, a_scale = standardizer(rows["a_seq"][train].reshape(-1, rows["a_seq"].shape[-1]))
    g_mean, g_scale = standardizer(rows["gap_hist"][train].reshape(-1, 1))
    t_mean, t_scale = standardizer(rows["t_features"][train])
    out["z_seq"] = apply_standardizer(rows["z_seq"].reshape(-1, rows["z_seq"].shape[-1]), z_mean, z_scale).reshape(rows["z_seq"].shape)
    out["a_seq"] = apply_standardizer(rows["a_seq"].reshape(-1, rows["a_seq"].shape[-1]), a_mean, a_scale).reshape(rows["a_seq"].shape)
    out["gap_hist"] = apply_standardizer(rows["gap_hist"].reshape(-1, 1), g_mean, g_scale).reshape(rows["gap_hist"].shape)
    out["t_features"] = apply_standardizer(rows["t_features"], t_mean, t_scale)
    return out


def predict(model: SequencePredictor, rows: dict[str, np.ndarray], mask: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    idx_all = np.where(mask)[0]
    out = np.zeros((len(idx_all), rows["current"].shape[1]), dtype=np.float32)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(idx_all), batch):
            idx = idx_all[start : start + batch]
            z = torch.from_numpy(rows["z_seq"][idx].astype(np.float32)).to(device)
            a = torch.from_numpy(rows["a_seq"][idx].astype(np.float32)).to(device)
            g = torch.from_numpy(rows["gap_hist"][idx].astype(np.float32)).to(device)
            tf = torch.from_numpy(rows["t_features"][idx].astype(np.float32)).to(device)
            delta = model(z, a, g, tf).detach().cpu().numpy().astype(np.float32)
            out[start : start + batch] = rows["current"][idx] + delta
    return out


def write_report(report: dict[str, Any], json_path: Path, md_path: Path) -> None:
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    lines = [
        "# Sequence Native Parity",
        "",
        f"- device: `{report['device']}`",
        f"- eval transitions: `{report['counts']['eval']}` across `{report['counts']['eval_episodes']}` episodes",
        f"- native MSE: `{report['metrics']['native_mse']['observed']:.9g}`",
        f"- LeWM MSE: `{report['metrics']['lewm_mse']['observed']:.9g}`",
        f"- trivial MSE: `{report['metrics']['trivial_mse']['observed']:.9g}`",
        f"- native/LeWM ratio: `{report['parity_gate']['native_to_lewm_ratio']:.9g}`",
        f"- parity pass: `{report['parity_gate']['pass']}`",
    ]
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a sequence-native next-latent parity candidate")
    parser.add_argument("--latents", default=str(ROOT / "tworooms_latent_large.npz"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=83)
    parser.add_argument("--epochs", type=int, default=220)
    parser.add_argument("--width", type=int, default=384)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=384)
    parser.add_argument("--lr", type=float, default=5.0e-4)
    parser.add_argument("--epsilon", type=float, default=0.10)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    latents_path = resolve_path(str(args.latents))
    rows_raw = build_rows(load_npz(latents_path))
    splits = split_episodes(int(np.max(rows_raw["episode"])) + 1, int(args.seed))
    masks = {name: np.isin(rows_raw["episode"], eps) for name, eps in splits.items()}
    train = masks["train"]
    cal = masks["calibration"]
    eval_mask = masks["eval"]
    rows = scale_rows(rows_raw, train)
    target_delta = (rows_raw["target"][train] - rows_raw["current"][train]).astype(np.float32)
    delta_mean, delta_scale = standardizer(target_delta)
    y_train = apply_standardizer(target_delta, delta_mean, delta_scale)
    model = SequencePredictor(rows["z_seq"].shape[-1], rows["a_seq"].shape[-1], int(args.width), int(args.depth)).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=float(args.lr), weight_decay=1.0e-4)
    train_idx = np.where(train)[0]
    rng = np.random.default_rng(int(args.seed) + 900)
    best_state = None
    best_cal = float("inf")
    history: list[dict[str, float]] = []
    for epoch in range(int(args.epochs)):
        model.train()
        order = rng.permutation(len(train_idx))
        losses: list[float] = []
        for start in range(0, len(order), int(args.batch)):
            idx = train_idx[order[start : start + int(args.batch)]]
            z = torch.from_numpy(rows["z_seq"][idx].astype(np.float32)).to(device)
            a = torch.from_numpy(rows["a_seq"][idx].astype(np.float32)).to(device)
            g = torch.from_numpy(rows["gap_hist"][idx].astype(np.float32)).to(device)
            tf = torch.from_numpy(rows["t_features"][idx].astype(np.float32)).to(device)
            y = torch.from_numpy(y_train[order[start : start + int(args.batch)]].astype(np.float32)).to(device)
            pred_delta = model(z, a, g, tf)
            loss = F.smooth_l1_loss(pred_delta, y)
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_pred = predict(model, rows, cal, device, int(args.batch))
        cal_target = rows_raw["target"][cal]
        cal_mse = float(np.mean(mse(cal_pred, cal_target)))
        history.append({"epoch": float(epoch + 1), "train": clean_float(float(np.mean(losses))), "cal_mse": clean_float(cal_mse)})
        if cal_mse < best_cal:
            best_cal = cal_mse
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    eval_pred = predict(model, rows, eval_mask, device, int(args.batch))
    eval_target = rows_raw["target"][eval_mask]
    eval_episode = rows_raw["episode"][eval_mask]
    native_mse = mse(eval_pred, eval_target)
    lewm_mse = rows_raw["lewm_mse"][eval_mask]
    trivial_mse = mse(rows_raw["current"][eval_mask], eval_target)
    parity_threshold = (1.0 + float(args.epsilon)) * float(np.mean(lewm_mse))
    parity_margin = parity_threshold - float(np.mean(native_mse))
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.sequence_native_parity",
        "device": str(device),
        "inputs": {"latents": str(latents_path)},
        "config": {
            "epochs": int(args.epochs),
            "width": int(args.width),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "epsilon": float(args.epsilon),
            "features": "GRU over latent history, GRU over future action-validity sequence, GRU over historical LeWM gap proxy, time features",
        },
        "counts": {
            "train": int(np.sum(train)),
            "calibration": int(np.sum(cal)),
            "eval": int(np.sum(eval_mask)),
            "eval_episodes": int(len(np.unique(eval_episode))),
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
    write_report(report, Path(args.json), Path(args.md))
    np.savez_compressed(
        Path(args.out),
        episode=eval_episode.astype(np.int64),
        t=rows_raw["t"][eval_mask].astype(np.int64),
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
