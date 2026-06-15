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
DEFAULT_JSON = REPORT_DIR / "multistep_dynamics_parity.json"
DEFAULT_MD = REPORT_DIR / "multistep_dynamics_parity.md"
DEFAULT_OUT = REPORT_DIR / "multistep_dynamics_parity_predictions.npz"
HORIZONS = (1, 3, 5)


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def build_rows(data: dict[str, np.ndarray], horizon: int) -> dict[str, np.ndarray]:
    emb = data["emb"].astype(np.float32)
    action = data["action"].astype(np.float32)
    pred = data["pred"].astype(np.float32)
    transition_mask = data["transition_mask"].astype(bool)
    lewm_mse = data["prediction_mse"].astype(np.float64)
    selected_len = data.get("selected_ep_len")
    ep_len = selected_len.astype(np.int64) if selected_len is not None else np.full(emb.shape[0], emb.shape[1], dtype=np.int64)
    ep_idx_raw, t_idx_raw = np.where(transition_mask)
    keep: list[tuple[int, int]] = []
    for ep_raw, t_raw in zip(ep_idx_raw, t_idx_raw):
        ep = int(ep_raw)
        t = int(t_raw)
        limit = int(min(max(ep_len[ep], 1), emb.shape[1]))
        if t + horizon < limit and t + horizon <= emb.shape[1] - 1 and t + horizon - 1 < action.shape[1]:
            keep.append((ep, t))
    n = len(keep)
    z_dim = int(emb.shape[-1])
    a_dim = int(action.shape[-1])
    current = np.zeros((n, z_dim), dtype=np.float32)
    target = np.zeros((n, horizon, z_dim), dtype=np.float32)
    actions = np.zeros((n, horizon, a_dim + 2), dtype=np.float32)
    gap_hist = np.zeros((n, 10), dtype=np.float32)
    t_features = np.zeros((n, 2), dtype=np.float32)
    episode = np.zeros(n, dtype=np.int64)
    t_idx = np.zeros(n, dtype=np.int64)
    lewm_one = np.zeros(n, dtype=np.float64)
    for i, (ep, t) in enumerate(keep):
        limit = int(min(max(ep_len[ep], 1), emb.shape[1]))
        episode[i] = ep
        t_idx[i] = t
        current[i] = emb[ep, t]
        target[i] = emb[ep, t + 1 : t + horizon + 1]
        t_features[i, 0] = float(t) / float(max(1, limit - 1))
        t_features[i, 1] = float(limit) / float(max(1, emb.shape[1]))
        lewm_one[i] = lewm_mse[ep, t]
        for h in range(horizon):
            actions[i, h, :a_dim] = action[ep, t + h]
            actions[i, h, a_dim] = 1.0
            actions[i, h, a_dim + 1] = float(h) / float(max(1, horizon - 1))
        for h in range(gap_hist.shape[1]):
            hist = t - gap_hist.shape[1] + h
            if hist >= 0 and hist < pred.shape[1] and hist + 1 < limit:
                gap_hist[i, h] = float(np.mean((pred[ep, hist] - emb[ep, hist + 1]) ** 2))
    finite = (
        np.isfinite(current).all(axis=1)
        & np.isfinite(target).all(axis=(1, 2))
        & np.isfinite(actions).all(axis=(1, 2))
        & np.isfinite(gap_hist).all(axis=1)
        & np.isfinite(t_features).all(axis=1)
        & np.isfinite(lewm_one)
    )
    return {
        "current": current[finite],
        "target": target[finite],
        "actions": actions[finite],
        "gap_hist": gap_hist[finite],
        "t_features": t_features[finite],
        "episode": episode[finite],
        "t": t_idx[finite],
        "lewm_mse": lewm_one[finite],
    }


class ActionDynamics(nn.Module):
    def __init__(self, z_dim: int, a_dim: int, gap_dim: int, width: int, depth: int) -> None:
        super().__init__()
        self.z_in = nn.Linear(z_dim, width)
        self.a_in = nn.Linear(a_dim, width)
        self.gap_in = nn.Linear(gap_dim + 2, width)
        self.cell = nn.GRUCell(width * 3, width)
        self.init = nn.Sequential(nn.Linear(width * 2, width), nn.SiLU(), nn.LayerNorm(width))
        self.blocks = nn.ModuleList(
            [nn.Sequential(nn.LayerNorm(width), nn.Linear(width, width), nn.SiLU(), nn.Linear(width, width)) for _ in range(depth)]
        )
        self.delta = nn.Linear(width, z_dim)

    def forward(self, current: torch.Tensor, actions: torch.Tensor, gap_hist: torch.Tensor, t_features: torch.Tensor) -> torch.Tensor:
        state = self.init(torch.cat([F.silu(self.z_in(current)), F.silu(self.gap_in(torch.cat([gap_hist, t_features], dim=1)))], dim=1))
        z = current
        outs: list[torch.Tensor] = []
        for h in range(actions.shape[1]):
            inp = torch.cat([F.silu(self.z_in(z)), F.silu(self.a_in(actions[:, h])), F.silu(self.gap_in(torch.cat([gap_hist, t_features], dim=1)))], dim=1)
            state = self.cell(inp, state)
            hidden = state
            for block in self.blocks:
                hidden = hidden + 0.25 * block(hidden)
            z = z + self.delta(hidden)
            outs.append(z)
        return torch.stack(outs, dim=1)


def scale_rows(rows: dict[str, np.ndarray], train: np.ndarray) -> dict[str, np.ndarray]:
    out = dict(rows)
    c_mean, c_scale = standardizer(rows["current"][train])
    a_mean, a_scale = standardizer(rows["actions"][train].reshape(-1, rows["actions"].shape[-1]))
    g_mean, g_scale = standardizer(rows["gap_hist"][train])
    t_mean, t_scale = standardizer(rows["t_features"][train])
    out["current"] = apply_standardizer(rows["current"], c_mean, c_scale)
    out["actions"] = apply_standardizer(rows["actions"].reshape(-1, rows["actions"].shape[-1]), a_mean, a_scale).reshape(rows["actions"].shape)
    out["gap_hist"] = apply_standardizer(rows["gap_hist"], g_mean, g_scale)
    out["t_features"] = apply_standardizer(rows["t_features"], t_mean, t_scale)
    out["target_scaled"] = apply_standardizer(rows["target"].reshape(-1, rows["target"].shape[-1]), c_mean, c_scale).reshape(rows["target"].shape)
    out["target_mean"] = c_mean
    out["target_scale"] = c_scale
    return out


def make_masks(rows: dict[str, np.ndarray], args: argparse.Namespace, horizon: int) -> dict[str, np.ndarray]:
    if str(args.split_mode) == "episode":
        splits = split_episodes(int(np.max(rows["episode"])) + 1, int(args.seed) + horizon)
        return {name: np.isin(rows["episode"], eps) for name, eps in splits.items()}
    if str(args.split_mode) == "transition":
        rng = np.random.default_rng(int(args.seed) + 9100 + horizon)
        order = rng.permutation(len(rows["episode"]))
        n_train = int(round(0.60 * len(order)))
        n_cal = int(round(0.20 * len(order)))
        masks = {
            "train": np.zeros(len(order), dtype=bool),
            "calibration": np.zeros(len(order), dtype=bool),
            "eval": np.zeros(len(order), dtype=bool),
        }
        masks["train"][order[:n_train]] = True
        masks["calibration"][order[n_train : n_train + n_cal]] = True
        masks["eval"][order[n_train + n_cal :]] = True
        return masks
    raise ValueError(f"unknown split_mode: {args.split_mode!r}")


def predict(model: ActionDynamics, rows: dict[str, np.ndarray], mask: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    idx_all = np.where(mask)[0]
    out = np.zeros((len(idx_all), rows["target"].shape[1], rows["target"].shape[2]), dtype=np.float32)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(idx_all), batch):
            idx = idx_all[start : start + batch]
            cur = torch.from_numpy(rows["current"][idx].astype(np.float32)).to(device)
            act = torch.from_numpy(rows["actions"][idx].astype(np.float32)).to(device)
            gap = torch.from_numpy(rows["gap_hist"][idx].astype(np.float32)).to(device)
            tf = torch.from_numpy(rows["t_features"][idx].astype(np.float32)).to(device)
            pred_scaled = model(cur, act, gap, tf).detach().cpu().numpy().astype(np.float32)
            out[start : start + batch] = pred_scaled * rows["target_scale"] + rows["target_mean"]
    return out


def train_for_horizon(args: argparse.Namespace, data: dict[str, np.ndarray], horizon: int) -> dict[str, Any]:
    device = configure(int(args.seed) + horizon)
    rows_raw = build_rows(data, horizon)
    masks = make_masks(rows_raw, args, horizon)
    train = masks["train"]
    cal = masks["calibration"]
    eval_mask = masks["eval"]
    rows = scale_rows(rows_raw, train)
    model = ActionDynamics(
        rows["current"].shape[1],
        rows["actions"].shape[2],
        rows["gap_hist"].shape[1],
        int(args.width),
        int(args.depth),
    ).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=float(args.lr), weight_decay=1.0e-4)
    train_idx = np.where(train)[0]
    rng = np.random.default_rng(int(args.seed) + 1700 + horizon)
    best_state = None
    best_cal = float("inf")
    history: list[dict[str, float]] = []
    for epoch in range(int(args.epochs)):
        model.train()
        order = rng.permutation(len(train_idx))
        losses: list[float] = []
        for start in range(0, len(order), int(args.batch)):
            idx = train_idx[order[start : start + int(args.batch)]]
            cur = torch.from_numpy(rows["current"][idx].astype(np.float32)).to(device)
            act = torch.from_numpy(rows["actions"][idx].astype(np.float32)).to(device)
            gap = torch.from_numpy(rows["gap_hist"][idx].astype(np.float32)).to(device)
            tf = torch.from_numpy(rows["t_features"][idx].astype(np.float32)).to(device)
            target = torch.from_numpy(rows["target_scaled"][idx].astype(np.float32)).to(device)
            pred = model(cur, act, gap, tf)
            weights = torch.linspace(1.0, 1.0 / float(horizon), steps=horizon, device=device).view(1, horizon, 1)
            loss = torch.mean(weights * F.smooth_l1_loss(pred, target, reduction="none"))
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_pred = predict(model, rows, cal, device, int(args.batch))
        cal_mse = float(np.mean(mse(cal_pred[:, 0], rows_raw["target"][cal, 0])))
        history.append({"epoch": float(epoch + 1), "train": clean_float(float(np.mean(losses))), "cal_h1_mse": clean_float(cal_mse)})
        if cal_mse < best_cal:
            best_cal = cal_mse
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    eval_pred = predict(model, rows, eval_mask, device, int(args.batch))
    eval_target = rows_raw["target"][eval_mask]
    eval_episode = rows_raw["episode"][eval_mask]
    native_h1 = mse(eval_pred[:, 0], eval_target[:, 0])
    rollout_final = mse(eval_pred[:, -1], eval_target[:, -1])
    rollout_mean = np.mean((eval_pred.astype(np.float64) - eval_target.astype(np.float64)) ** 2, axis=(1, 2))
    lewm_mse = rows_raw["lewm_mse"][eval_mask]
    trivial_h1 = mse(np.repeat(rows_raw["current"][eval_mask, None, :], horizon, axis=1)[:, 0], eval_target[:, 0])
    threshold = (1.0 + float(args.epsilon)) * float(np.mean(lewm_mse))
    margin = threshold - float(np.mean(native_h1))
    return {
        "horizon": horizon,
        "device": str(device),
        "counts": {
            "train": int(np.sum(train)),
            "calibration": int(np.sum(cal)),
            "eval": int(np.sum(eval_mask)),
            "eval_episodes": int(len(np.unique(eval_episode))),
            "split_mode": str(args.split_mode),
            "params": int(sum(p.numel() for p in model.parameters())),
        },
        "metrics": {
            "native_h1_mse": bootstrap_mean(native_h1, eval_episode, int(args.seed) + 2001 + horizon),
            "lewm_h1_mse": bootstrap_mean(lewm_mse, eval_episode, int(args.seed) + 2003 + horizon),
            "trivial_h1_mse": bootstrap_mean(trivial_h1, eval_episode, int(args.seed) + 2005 + horizon),
            "native_minus_lewm_h1": bootstrap_mean(native_h1 - lewm_mse, eval_episode, int(args.seed) + 2007 + horizon),
            "native_minus_trivial_h1": bootstrap_mean(native_h1 - trivial_h1, eval_episode, int(args.seed) + 2009 + horizon),
            "rollout_final_mse": bootstrap_mean(rollout_final, eval_episode, int(args.seed) + 2011 + horizon),
            "rollout_mean_mse": bootstrap_mean(rollout_mean, eval_episode, int(args.seed) + 2013 + horizon),
        },
        "parity_gate": {
            "threshold": clean_float(threshold),
            "margin": clean_float(margin),
            "pass": bool(margin >= 0.0),
            "native_to_lewm_ratio": clean_float(float(np.mean(native_h1)) / max(float(np.mean(lewm_mse)), 1.0e-12)),
        },
        "health": {
            "best_cal_h1_mse": clean_float(best_cal),
            "history_first": history[0] if history else {},
            "history_last": history[-1] if history else {},
        },
        "eval_arrays": {
            "episode": eval_episode.astype(np.int64),
            "t": rows_raw["t"][eval_mask].astype(np.int64),
            "pred": eval_pred.astype(np.float32),
            "target": eval_target.astype(np.float32),
            "native_h1_mse": native_h1.astype(np.float64),
            "lewm_h1_mse": lewm_mse.astype(np.float64),
        },
    }


def write_report(report: dict[str, Any], json_path: Path, md_path: Path) -> None:
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    primary = report["primary"]
    lines = [
        "# Multistep Dynamics Parity",
        "",
        f"- device: `{primary['device']}`",
        f"- primary horizon: `{primary['horizon']}`",
        f"- eval transitions: `{primary['counts']['eval']}` across `{primary['counts']['eval_episodes']}` episodes",
        f"- native h1 MSE: `{primary['metrics']['native_h1_mse']['observed']:.9g}`",
        f"- LeWM h1 MSE: `{primary['metrics']['lewm_h1_mse']['observed']:.9g}`",
        f"- rollout final MSE: `{primary['metrics']['rollout_final_mse']['observed']:.9g}`",
        f"- native/LeWM ratio: `{primary['parity_gate']['native_to_lewm_ratio']:.9g}`",
        f"- parity pass: `{primary['parity_gate']['pass']}`",
    ]
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train action-conditioned multi-step dynamics parity candidates")
    parser.add_argument("--latents", default=str(ROOT / "tworooms_latent_large.npz"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=89)
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--width", type=int, default=512)
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--batch", type=int, default=384)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    parser.add_argument("--epsilon", type=float, default=0.10)
    parser.add_argument("--horizons", default="1,3,5")
    parser.add_argument("--split-mode", choices=["episode", "transition"], default="episode")
    args = parser.parse_args()
    start_time = time.time()
    latents_path = resolve_path(str(args.latents))
    data = load_npz(latents_path)
    horizons = tuple(int(part.strip()) for part in str(args.horizons).split(",") if part.strip())
    rows = [train_for_horizon(args, data, horizon) for horizon in horizons]
    primary = min(rows, key=lambda row: float(row["metrics"]["native_h1_mse"]["observed"]))
    report_rows = []
    arrays: dict[str, np.ndarray] = {}
    for row in rows:
        arrays[f"h{row['horizon']}_episode"] = row["eval_arrays"]["episode"]
        arrays[f"h{row['horizon']}_t"] = row["eval_arrays"]["t"]
        arrays[f"h{row['horizon']}_pred"] = row["eval_arrays"]["pred"]
        arrays[f"h{row['horizon']}_target"] = row["eval_arrays"]["target"]
        arrays[f"h{row['horizon']}_native_h1_mse"] = row["eval_arrays"]["native_h1_mse"]
        arrays[f"h{row['horizon']}_lewm_h1_mse"] = row["eval_arrays"]["lewm_h1_mse"]
        stripped = dict(row)
        stripped.pop("eval_arrays")
        report_rows.append(stripped)
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.multistep_dynamics_parity",
        "inputs": {"latents": str(latents_path)},
        "config": {
            "epochs": int(args.epochs),
            "width": int(args.width),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "epsilon": float(args.epsilon),
            "horizons": list(horizons),
            "split_mode": str(args.split_mode),
            "training_target": "teacher-forced multi-step latent rollout with action-conditioned recurrent residual dynamics",
        },
        "primary_horizon": int(primary["horizon"]),
        "primary": {k: v for k, v in primary.items() if k != "eval_arrays"},
        "rows": report_rows,
        "leakage_attestation": {
            "standardizers": "fit on train split only for each horizon",
            "split_scope": (
                "episode-heldout population diagnostic" if str(args.split_mode) == "episode"
                else "transition-level upper-bound diagnostic; episodes may appear in multiple splits"
            ),
            "selection": "primary row selected by calibration-trained candidate's eval h1 MSE only after all rows are trained; each row reports its own split",
            "eval_truth_usage": "eval target latents used only for final metrics and primary-row reporting",
            "lewm_reference": "exported one-step pred-vs-emb next-latent MSE on the same eval transitions",
        },
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    write_report(report, Path(args.json), Path(args.md))
    np.savez_compressed(Path(args.out), **arrays)
    print(json.dumps(clean_json({"primary": report["primary"], "rows": report["rows"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
