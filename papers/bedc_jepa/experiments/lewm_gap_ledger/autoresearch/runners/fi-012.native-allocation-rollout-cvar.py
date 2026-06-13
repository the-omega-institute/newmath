#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
from collections import defaultdict
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


ROOT = Path(__file__).resolve().parents[2]
LATENT_NPZ = ROOT / "tworooms_latent_large.npz"
CLEAN_LABELS = ROOT / "reports" / "g2n_labels_clean.npz"

HYPOTHESIS_ID = "fi-012.native-allocation-rollout-cvar"
METRIC = "allocation_delta"

WINDOW = 6
ROLLOUT_H = 5
TARGET_H = 5
TARGET_H_INDEX = TARGET_H - 1
UNIFORM_H = 3
LOW_H = 5
MID_H = 3
HIGH_H = 1
ALPHA = 0.10
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
HORIZON_EPOCHS = 70
ALLOC_EPOCHS = 80
BATCH = 192
LR = 1.0e-3
WEIGHT_DECAY = 1.0e-4
CVAR_WEIGHT = 4.0
TAIL_Q = 75.0
EPS = 1.0e-8


def configure_determinism(seed: int) -> torch.device:
    os.environ["PYTHONHASHSEED"] = str(seed)
    os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    torch.backends.cuda.matmul.allow_tf32 = False
    torch.backends.cudnn.allow_tf32 = False
    try:
        torch.set_float32_matmul_precision("highest")
    except AttributeError:
        pass
    try:
        torch.set_num_threads(1)
        torch.set_num_interop_threads(1)
    except RuntimeError:
        pass
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite float for JSON payload: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, np.integer):
        return int(value)
    if isinstance(value, np.floating):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as raw:
        return {k: raw[k] for k in raw.files}


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = x.mean(axis=0, dtype=np.float64).astype(np.float32)
    scale = x.std(axis=0, dtype=np.float64).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x - mean) / scale).astype(np.float32)


def sigmoid_np(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


def rank_average(x: np.ndarray) -> np.ndarray:
    order = np.argsort(x, kind="mergesort")
    ranks = np.empty(len(x), dtype=np.float64)
    i = 0
    while i < len(x):
        j = i + 1
        while j < len(x) and x[order[j]] == x[order[i]]:
            j += 1
        ranks[order[i:j]] = (i + 1 + j) / 2.0
        i = j
    return ranks


def auroc_rank(y_true: np.ndarray, score: np.ndarray) -> float:
    y = y_true.astype(bool)
    n_pos = int(y.sum())
    n_neg = int((~y).sum())
    if n_pos == 0 or n_neg == 0:
        return 0.5
    ranks = rank_average(score.astype(np.float64))
    return float((ranks[y].sum() - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg))


def spearman_one(x: np.ndarray, y: np.ndarray) -> float:
    if len(x) < 2:
        return float("nan")
    rx = rank_average(x.astype(np.float64))
    ry = rank_average(y.astype(np.float64))
    if float(np.std(rx)) == 0.0 or float(np.std(ry)) == 0.0:
        return float("nan")
    return float(np.corrcoef(rx, ry)[0, 1])


def split_by_episode_indices(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0] for ep in np.unique(episode)]


def build_base_features(
    data: dict[str, np.ndarray],
    labels: dict[str, np.ndarray],
    split: str,
) -> dict[str, np.ndarray]:
    anchors = labels[f"{split}_anchor_ep_t0"].astype(np.int64)
    emb = data["emb"].astype(np.float32)
    action = data["action"].astype(np.float32)
    transition_mask = data["transition_mask"].astype(bool)
    pred_z = labels[f"{split}_pred_z"][:, :ROLLOUT_H].astype(np.float32)
    valid = labels[f"{split}_valid"][:, :ROLLOUT_H].astype(bool)
    past_gap = data["prediction_mse"].astype(np.float32)

    n = len(anchors)
    emb_dim = int(emb.shape[-1])
    act_dim = int(action.shape[-1])
    past_z = np.zeros((n, WINDOW, emb_dim), dtype=np.float32)
    past_a = np.zeros((n, WINDOW, act_dim), dtype=np.float32)
    current_z = np.zeros((n, emb_dim), dtype=np.float32)
    pred_delta = np.zeros((n, ROLLOUT_H, emb_dim), dtype=np.float32)
    gap_hist = np.zeros((n, WINDOW), dtype=np.float32)
    t_scalar = np.zeros((n, 1), dtype=np.float32)
    valid_count_scalar = np.zeros((n, 1), dtype=np.float32)

    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t = int(t_raw)
        valid_count = int(transition_mask[ep].sum())
        denom = float(max(1, valid_count - 1))
        t_scalar[i, 0] = float(t) / denom
        valid_count_scalar[i, 0] = float(valid_count) / float(max(1, transition_mask.shape[1]))
        current_z[i] = emb[ep, t]
        previous = emb[ep, t]
        for w in range(WINDOW):
            src = max(0, t - WINDOW + 1 + w)
            past_z[i, w] = emb[ep, src]
            past_a[i, w] = action[ep, src]
            # Non-leaking historical gap: this excludes prediction_mse[ep,t]
            # and all t..t+4 target-budget errors used for allocation scoring.
            gap_src = max(0, t - WINDOW + w)
            gap_hist[i, w] = past_gap[ep, gap_src] if gap_src < t else 0.0
        for k in range(ROLLOUT_H):
            if valid[i, k] and np.isfinite(pred_z[i, k]).all():
                pred_delta[i, k] = pred_z[i, k] - previous
                previous = pred_z[i, k]
            else:
                pred_z[i, k] = 0.0
                pred_delta[i, k] = 0.0

    drift = np.linalg.norm(pred_delta, axis=2).astype(np.float32)
    curvature_vec = pred_delta[:, 1:, :] - pred_delta[:, :-1, :]
    curvature = np.linalg.norm(curvature_vec, axis=2).astype(np.float32)
    spread = np.linalg.norm(pred_z - current_z[:, None, :], axis=2).astype(np.float32)
    gap_hist = np.where(np.isfinite(gap_hist), gap_hist, 0.0).astype(np.float32)
    stats = np.concatenate(
        [
            valid.astype(np.float32),
            drift,
            spread,
            curvature,
            drift.mean(axis=1, keepdims=True),
            drift.max(axis=1, keepdims=True),
            drift.std(axis=1, keepdims=True),
            spread[:, -1:].astype(np.float32),
            curvature.mean(axis=1, keepdims=True),
            curvature.max(axis=1, keepdims=True),
            gap_hist,
            gap_hist.mean(axis=1, keepdims=True),
            gap_hist.max(axis=1, keepdims=True),
            t_scalar,
            valid_count_scalar,
        ],
        axis=1,
    ).astype(np.float32)

    # Feature audit:
    # - current_z and past_z/past_a are observed at or before anchor t.
    # - pred_z is labels[*_pred_z], the predictor's own rollout trajectory.
    # - pred_delta, drift, spread, and curvature are deterministic transforms of
    #   current_z and pred_z only.
    # - gap_hist uses prediction_mse strictly before t, never t..t+4.
    # - No eval target column err_at_h or mean_err_to_h is used in features.
    base = np.concatenate(
        [
            current_z,
            past_z.reshape(n, -1),
            past_a.reshape(n, -1),
            pred_z.reshape(n, -1),
            pred_delta.reshape(n, -1),
            stats,
        ],
        axis=1,
    ).astype(np.float32)
    base = np.where(np.isfinite(base), base, 0.0).astype(np.float32)
    return {
        "x": base,
        "anchor_ep_t0": anchors,
        "episode": anchors[:, 0].astype(np.int64),
    }


class HorizonLedger(nn.Module):
    def __init__(self, in_dim: int, out_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, 160),
            nn.ReLU(),
            nn.Linear(160, 96),
            nn.ReLU(),
            nn.Linear(96, out_dim),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class AllocationHead(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, 128),
            nn.ReLU(),
            nn.Linear(128, 64),
            nn.ReLU(),
            nn.Linear(64, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


class PosthocHead(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(nn.Linear(in_dim, 64), nn.ReLU(), nn.Linear(64, 1))

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def train_horizon_ledger(
    x_train: np.ndarray,
    y_train: np.ndarray,
    valid_train: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> HorizonLedger:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = HorizonLedger(x_train.shape[1], y_train.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_train.astype(np.float32)).to(device)
    v_t = torch.from_numpy(valid_train.astype(bool)).to(device)
    generator = torch.Generator(device="cpu").manual_seed(seed + 1009)
    n = len(x_train)
    model.train()
    for _ in range(HORIZON_EPOCHS):
        order = torch.randperm(n, generator=generator)
        for lo in range(0, n, BATCH):
            idx = order[lo : lo + BATCH].to(device)
            logits = model(x_t[idx])
            per = F.binary_cross_entropy_with_logits(logits, y_t[idx], reduction="none")
            mask = v_t[idx].float()
            loss = (per * mask).sum() / mask.sum().clamp_min(1.0)
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite horizon ledger loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


def predict_horizon_logits(model: HorizonLedger, x: np.ndarray, device: torch.device) -> np.ndarray:
    out = np.zeros((len(x), model.net[-1].out_features), dtype=np.float32)
    with torch.inference_mode():
        for lo in range(0, len(x), 512):
            hi = min(lo + 512, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            out[lo:hi] = model(xb).detach().cpu().numpy().astype(np.float32)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return out


def pairwise_tail_rank_loss(
    score: torch.Tensor,
    target: torch.Tensor,
    episode: torch.Tensor,
    tail_weight: torch.Tensor,
) -> torch.Tensor | None:
    same = episode[:, None] == episode[None, :]
    upper = torch.triu(torch.ones_like(same, dtype=torch.bool), diagonal=1)
    diff = target[:, None] - target[None, :]
    sign = torch.sign(diff)
    pair = same & upper & (sign != 0)
    if not bool(pair.any()):
        return None
    score_diff = score[:, None] - score[None, :]
    weights = 0.5 * (tail_weight[:, None] + tail_weight[None, :])
    per = F.softplus(-(score_diff[pair] * sign[pair]))
    return (per * weights[pair]).sum() / weights[pair].sum().clamp_min(1.0)


def train_allocation_head(
    x_train: np.ndarray,
    y_mean_h5: np.ndarray,
    cvar_tail: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> AllocationHead:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    tail_cut = float(np.percentile(cvar_tail, TAIL_Q))
    tail_indicator = (cvar_tail >= tail_cut).astype(np.float32)
    tail_weight_np = (1.0 + CVAR_WEIGHT * tail_indicator).astype(np.float32)
    target_log_np = np.log(y_mean_h5.astype(np.float64) + EPS).astype(np.float32)

    model = AllocationHead(x_train.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_mean_h5.astype(np.float32)).to(device)
    y_log_t = torch.from_numpy(target_log_np).to(device)
    ep_t = torch.from_numpy(episode.astype(np.int64)).to(device)
    tw_t = torch.from_numpy(tail_weight_np).to(device)
    generator = torch.Generator(device="cpu").manual_seed(seed + 2027)
    n = len(x_train)
    model.train()
    for _ in range(ALLOC_EPOCHS):
        order = torch.randperm(n, generator=generator)
        for lo in range(0, n, BATCH):
            idx = order[lo : lo + BATCH].to(device)
            score = model(x_t[idx])
            rank_loss = pairwise_tail_rank_loss(score, y_t[idx], ep_t[idx], tw_t[idx])
            centered = (y_log_t[idx] - torch.mean(y_log_t[idx])).detach()
            reg = F.smooth_l1_loss(score - torch.mean(score), centered, reduction="none")
            reg = (reg * tw_t[idx]).sum() / tw_t[idx].sum().clamp_min(1.0)
            loss = reg if rank_loss is None else rank_loss + 0.15 * reg
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite allocation loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


def predict_scalar(model: nn.Module, x: np.ndarray, device: torch.device) -> np.ndarray:
    out = np.zeros(len(x), dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, len(x), 512):
            hi = min(lo + 512, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            out[lo:hi] = model(xb).detach().cpu().numpy().astype(np.float64)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return out


def train_posthoc_head(
    x_train: np.ndarray,
    y_train: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> PosthocHead:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = PosthocHead(x_train.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_train.astype(np.float32)).to(device)
    pos = float(y_train.sum())
    neg = float(len(y_train) - y_train.sum())
    pos_weight = torch.tensor([neg / max(pos, 1.0)], dtype=torch.float32, device=device)
    generator = torch.Generator(device="cpu").manual_seed(seed + 3037)
    model.train()
    for _ in range(70):
        order = torch.randperm(len(y_train), generator=generator)
        for lo in range(0, len(y_train), BATCH):
            idx = order[lo : lo + BATCH].to(device)
            logits = model(x_t[idx])
            loss = F.binary_cross_entropy_with_logits(logits, y_t[idx], pos_weight=pos_weight)
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite posthoc loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


def anchors_by_episode(anchors: np.ndarray) -> dict[int, list[int]]:
    out: dict[int, list[int]] = defaultdict(list)
    for i, (ep, _) in enumerate(anchors):
        out[int(ep)].append(i)
    return out


def allocation_by_score(anchors: np.ndarray, by_ep: dict[int, list[int]], score: np.ndarray) -> np.ndarray:
    h = np.zeros(len(anchors), dtype=np.int64)
    for idxs in by_ep.values():
        ordered = sorted(idxs, key=lambda i: (float(score[i]), int(anchors[i, 1]), i))
        n = len(ordered)
        half = n // 2
        h[np.asarray(ordered[:half], dtype=np.int64)] = LOW_H
        h[np.asarray(ordered[n - half :], dtype=np.int64)] = HIGH_H
        if n % 2:
            h[ordered[half]] = MID_H
        if int(h[np.asarray(idxs, dtype=np.int64)].sum()) != UNIFORM_H * n:
            raise RuntimeError("episode allocation budget mismatch")
    return h


def allocation_uniform(by_ep: dict[int, list[int]]) -> np.ndarray:
    h = np.zeros(sum(len(v) for v in by_ep.values()), dtype=np.int64)
    for idxs in by_ep.values():
        h[np.asarray(idxs, dtype=np.int64)] = UNIFORM_H
    return h


def summarize_allocation(h: np.ndarray, errors_h5: np.ndarray, anchors: np.ndarray) -> dict[str, Any]:
    anchor_error = np.asarray([float(errors_h5[i, : int(h_i)].sum()) for i, h_i in enumerate(h)], dtype=np.float64)
    by_ep_error: dict[str, float] = defaultdict(float)
    by_ep_steps: dict[str, int] = defaultdict(int)
    for i, (ep_raw, _) in enumerate(anchors):
        ep = str(int(ep_raw))
        by_ep_error[ep] += float(anchor_error[i])
        by_ep_steps[ep] += int(h[i])
    return {
        "episode_total_error": {k: float(by_ep_error[k]) for k in sorted(by_ep_error, key=int)},
        "episode_emitted_steps": {k: int(by_ep_steps[k]) for k in sorted(by_ep_steps, key=int)},
    }


def paired_allocation_delta(
    ledger: dict[str, Any],
    uniform: dict[str, Any],
    *,
    seed: int,
) -> dict[str, float]:
    a_err = ledger["episode_total_error"]
    b_err = uniform["episode_total_error"]
    a_steps = ledger["episode_emitted_steps"]
    b_steps = uniform["episode_emitted_steps"]
    eps = sorted(b_err.keys(), key=int)
    if eps != sorted(a_err.keys(), key=int):
        raise RuntimeError("episode keys differ in allocation bootstrap")
    ae = np.asarray([a_err[ep] for ep in eps], dtype=np.float64)
    be = np.asarray([b_err[ep] for ep in eps], dtype=np.float64)
    ast = np.asarray([a_steps[ep] for ep in eps], dtype=np.float64)
    bst = np.asarray([b_steps[ep] for ep in eps], dtype=np.float64)
    observed = float(ae.sum() / ast.sum() - be.sum() / bst.sum())
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        idx = rng.integers(0, len(eps), size=len(eps))
        samples[i] = float(ae[idx].sum() / ast[idx].sum() - be[idx].sum() / bst[idx].sum())
    return {
        "observed": observed,
        "low": float(np.percentile(samples, 2.5)),
        "high": float(np.percentile(samples, 97.5)),
    }


def bootstrap_spearman(score: np.ndarray, truth: np.ndarray, episode: np.ndarray, *, seed: int) -> dict[str, float]:
    by_ep = split_by_episode_indices(episode)
    vals: list[float] = []
    for idx in by_ep:
        rho = spearman_one(score[idx], truth[idx])
        if np.isfinite(rho):
            vals.append(float(rho))
    observed = float(np.mean(vals)) if vals else float("nan")
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    vals_np = np.asarray(vals, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(vals_np), size=len(vals_np))
        samples[i] = float(vals_np[pick].mean())
    return {
        "observed": observed,
        "low": float(np.percentile(samples, 2.5)),
        "high": float(np.percentile(samples, 97.5)),
    }


def paired_auroc_delta(
    y: np.ndarray,
    native_score: np.ndarray,
    posthoc_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
) -> dict[str, float]:
    observed_native = auroc_rank(y, native_score)
    observed_posthoc = auroc_rank(y, posthoc_score)
    by_ep = split_by_episode_indices(episode)
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in pick])
        if np.unique(y[idx]).size < 2:
            samples[i] = 0.0
        else:
            samples[i] = auroc_rank(y[idx], native_score[idx]) - auroc_rank(y[idx], posthoc_score[idx])
    return {
        "observed": float(observed_native - observed_posthoc),
        "low": float(np.percentile(samples, 2.5)),
        "high": float(np.percentile(samples, 97.5)),
        "native": float(observed_native),
        "posthoc": float(observed_posthoc),
    }


def selective_threshold(score: np.ndarray, y: np.ndarray, alpha: float) -> float | None:
    order = np.argsort(score, kind="mergesort")
    sorted_score = score[order]
    sorted_y = y[order].astype(np.float64)
    cum_fail = np.cumsum(sorted_y)
    n = np.arange(1, len(sorted_y) + 1, dtype=np.float64)
    risk = cum_fail / n
    ok = np.where(risk <= alpha)[0]
    if len(ok) == 0:
        return None
    return float(sorted_score[int(ok[-1])])


def selective_risk(score: np.ndarray, y: np.ndarray, threshold: float | None) -> dict[str, float | None]:
    if threshold is None:
        return {"risk": None, "coverage": 0.0}
    keep = score <= threshold
    coverage = float(np.mean(keep)) if len(score) else 0.0
    risk = float(np.mean(y[keep])) if bool(keep.any()) else None
    return {"risk": risk, "coverage": coverage}


def verdict_from_delta(ci_low: float, ci_high: float) -> str:
    if ci_high < 0.0:
        return "positive"
    if ci_low >= 0.0:
        return "negative"
    return "unidentifiable"


def make_fail_payload(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["allocation_delta", "auroc", "uer"],
        "reported_claim": f"fail-closed：{reason}；未报告 allocation 改善。",
    }


def build_claim(delta: dict[str, float], rho: dict[str, float], auroc: dict[str, float], sel: dict[str, float | None], verdict: str) -> str:
    risk = "NA" if sel["risk"] is None else f"{float(sel['risk']):.6f}"
    if float(rho["low"]) > 0.5:
        ceiling = "CI 下界高于 0.5，稳健越过历史 ρ≈0.5"
    elif float(rho["observed"]) >= 0.5:
        ceiling = "点估计略高于 0.5，但 CI 覆盖 0.5，未稳健突破历史 ρ≈0.5"
    else:
        ceiling = "未破历史 ρ≈0.5"
    if verdict == "positive":
        decision = "CI high<0，allocation 闭合"
    elif verdict == "negative":
        decision = "CI low>=0，未改善且方向为负结果"
    else:
        decision = "CI 跨 0，不可识别为改善"
    return (
        f"rollout-native CVaR/tail-rank allocation_delta={delta['observed']:.9g}, "
        f"95% CI=[{delta['low']:.9g},{delta['high']:.9g}]；{decision}。"
        f"Spearman ρ={rho['observed']:.6f} [{rho['low']:.6f},{rho['high']:.6f}]，{ceiling}。"
        f"paired native-vs-posthoc h1 ΔAUROC={auroc['observed']:.6f} "
        f"[{auroc['low']:.6f},{auroc['high']:.6f}] "
        f"(native={auroc['native']:.6f}, posthoc={auroc['posthoc']:.6f})。"
        f"α=0.10 selective risk={risk}, coverage={float(sel['coverage']):.6f}。"
    )


def build_payload(seed: int) -> dict[str, Any]:
    device = configure_determinism(seed)
    if not LATENT_NPZ.exists() or not CLEAN_LABELS.exists():
        return make_fail_payload("缺少 tworooms latent 或 g2n clean labels 输入")

    data = load_npz(LATENT_NPZ)
    labels = load_npz(CLEAN_LABELS)
    required = [
        "train_anchor_ep_t0",
        "train_pred_z",
        "train_valid",
        "train_y",
        "train_err_at_h",
        "train_mean_err_to_h",
        "calibration_anchor_ep_t0",
        "calibration_pred_z",
        "calibration_valid",
        "calibration_y",
        "eval_anchor_ep_t0",
        "eval_pred_z",
        "eval_valid",
        "eval_y",
        "eval_err_at_h",
        "eval_mean_err_to_h",
    ]
    missing = [k for k in required if k not in labels]
    if missing:
        return make_fail_payload("clean labels 字段缺失：" + ",".join(missing))

    train_rows = build_base_features(data, labels, "train")
    cal_rows = build_base_features(data, labels, "calibration")
    eval_rows = build_base_features(data, labels, "eval")

    train_mean, train_scale = fit_standardizer(train_rows["x"])
    x_train_base = apply_standardizer(train_rows["x"], train_mean, train_scale)
    x_cal_base = apply_standardizer(cal_rows["x"], train_mean, train_scale)
    x_eval_base = apply_standardizer(eval_rows["x"], train_mean, train_scale)

    y_train_all = labels["train_y"].reshape(len(train_rows["x"]), -1).astype(np.float32)
    v_train_all = np.repeat(labels["train_valid"][:, :, None], labels["train_y"].shape[2], axis=2).reshape(len(train_rows["x"]), -1)
    horizon = train_horizon_ledger(
        x_train_base,
        y_train_all,
        v_train_all,
        seed=seed + 11,
        device=device,
    )
    train_logits = predict_horizon_logits(horizon, x_train_base, device)
    cal_logits = predict_horizon_logits(horizon, x_cal_base, device)
    eval_logits = predict_horizon_logits(horizon, x_eval_base, device)

    x_train_alloc_all = np.concatenate([x_train_base, train_logits], axis=1).astype(np.float32)
    x_cal_alloc_all = np.concatenate([x_cal_base, cal_logits], axis=1).astype(np.float32)
    x_eval_alloc_all = np.concatenate([x_eval_base, eval_logits], axis=1).astype(np.float32)
    alloc_mean, alloc_scale = fit_standardizer(x_train_alloc_all)
    x_train_alloc_all = apply_standardizer(x_train_alloc_all, alloc_mean, alloc_scale)
    x_cal_alloc_all = apply_standardizer(x_cal_alloc_all, alloc_mean, alloc_scale)
    x_eval_alloc_all = apply_standardizer(x_eval_alloc_all, alloc_mean, alloc_scale)

    train_h5_valid = labels["train_valid"][:, TARGET_H_INDEX].astype(bool)
    eval_h5_valid = labels["eval_valid"][:, TARGET_H_INDEX].astype(bool)
    if int(train_h5_valid.sum()) == 0 or int(eval_h5_valid.sum()) == 0:
        return make_fail_payload("train/eval h=5 有效 anchor 为空")

    train_target = labels["train_mean_err_to_h"][train_h5_valid, TARGET_H_INDEX].astype(np.float64)
    train_cvar = np.max(labels["train_err_at_h"][train_h5_valid, :TARGET_H].astype(np.float64), axis=1)
    train_episode = train_rows["episode"][train_h5_valid].astype(np.int64)
    if len(np.unique(train_episode)) < 2 or len(np.unique(eval_rows["episode"][eval_h5_valid])) < 2:
        return make_fail_payload("episode split 过少，episode bootstrap 不可识别")

    alloc_model = train_allocation_head(
        x_train_alloc_all[train_h5_valid],
        train_target,
        train_cvar,
        train_episode,
        seed=seed + 23,
        device=device,
    )
    eval_score = predict_scalar(alloc_model, x_eval_alloc_all[eval_h5_valid], device)

    eval_anchors = eval_rows["anchor_ep_t0"][eval_h5_valid].astype(np.int64)
    errors_h5 = labels["eval_err_at_h"][eval_h5_valid, :TARGET_H].astype(np.float64)
    true_mean_h5 = labels["eval_mean_err_to_h"][eval_h5_valid, TARGET_H_INDEX].astype(np.float64)
    by_ep = anchors_by_episode(eval_anchors)
    uniform_alloc = summarize_allocation(allocation_uniform(by_ep), errors_h5, eval_anchors)
    ledger_alloc = summarize_allocation(allocation_by_score(eval_anchors, by_ep, eval_score), errors_h5, eval_anchors)
    delta = paired_allocation_delta(ledger_alloc, uniform_alloc, seed=seed + BOOTSTRAP_SEED_OFFSET)
    rho = bootstrap_spearman(eval_score, true_mean_h5, eval_rows["episode"][eval_h5_valid], seed=seed + BOOTSTRAP_SEED_OFFSET + 1)

    h1_col = 0 * labels["train_y"].shape[2] + 1
    train_h1_valid = labels["train_valid"][:, 0].astype(bool)
    cal_h1_valid = labels["calibration_valid"][:, 0].astype(bool)
    eval_h1_valid = labels["eval_valid"][:, 0].astype(bool)
    train_y_h1 = labels["train_y"][train_h1_valid, 0, 1].astype(np.int8)
    eval_y_h1 = labels["eval_y"][eval_h1_valid, 0, 1].astype(np.int8)
    if np.unique(train_y_h1).size < 2 or np.unique(eval_y_h1).size < 2:
        return make_fail_payload("h=1 detection 标签单类")

    current_dim = int(data["emb"].shape[-1])
    z_train = x_train_base[train_h1_valid, :current_dim]
    z_eval = x_eval_base[eval_h1_valid, :current_dim]
    posthoc = train_posthoc_head(z_train, train_y_h1, seed=seed + 37, device=device)
    posthoc_eval_score = predict_scalar(posthoc, z_eval, device)
    native_eval_score = eval_logits[eval_h1_valid, h1_col].astype(np.float64)
    auroc = paired_auroc_delta(
        eval_y_h1,
        native_eval_score,
        posthoc_eval_score,
        eval_rows["episode"][eval_h1_valid],
        seed=seed + BOOTSTRAP_SEED_OFFSET + 2,
    )

    cal_score = cal_logits[cal_h1_valid, h1_col].astype(np.float64)
    cal_y = labels["calibration_y"][cal_h1_valid, 0, 1].astype(np.int8)
    threshold = selective_threshold(cal_score, cal_y, ALPHA)
    sel = selective_risk(native_eval_score, eval_y_h1, threshold)

    verdict = verdict_from_delta(delta["low"], delta["high"])
    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": float(delta["observed"]),
        "ci": {"low": float(delta["low"]), "high": float(delta["high"])},
        "measured_scope": ["allocation_delta", "auroc", "uer"],
        "reported_claim": build_claim(delta, rho, auroc, sel, verdict),
    }
    if verdict == "unidentifiable":
        payload["status"] = "fail-closed"
    if torch.cuda.is_available():
        torch.cuda.empty_cache()
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = clean_json(build_payload(int(args.seed)))
    claim = str(payload.get("reported_claim", ""))
    forbidden = ("real_robot_transfer", "paper_claim_strength")
    if any(token in claim for token in forbidden):
        raise RuntimeError("reported_claim contains a forbidden scope token")
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
