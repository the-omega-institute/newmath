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

HYPOTHESIS_ID = "fi-013.allocation-representation-shaping"
METRIC = "allocation_delta"

TARGET_H = 5
TARGET_H_INDEX = TARGET_H - 1
Q75_INDEX = 1
UNIFORM_H = 3
LOW_H = 5
MID_H = 3
HIGH_H = 1
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
BATCH = 192
EPOCHS = 100
LR = 8.0e-4
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


def build_latent_rows(
    data: dict[str, np.ndarray],
    labels: dict[str, np.ndarray],
    split: str,
) -> dict[str, np.ndarray]:
    anchors = labels[f"{split}_anchor_ep_t0"].astype(np.int64)
    emb = data["emb"].astype(np.float32)
    target = data["transition_target_emb"].astype(np.float32)
    transition_mask = data["transition_mask"].astype(bool)
    n = len(anchors)
    dim = int(emb.shape[-1])
    x = np.zeros((n, dim), dtype=np.float32)
    next_z = np.zeros((n, dim), dtype=np.float32)
    next_valid = np.zeros(n, dtype=bool)
    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t = int(t_raw)
        x[i] = emb[ep, t]
        if t < target.shape[1] and transition_mask[ep, t]:
            next_z[i] = target[ep, t]
            next_valid[i] = True
        else:
            next_z[i] = emb[ep, min(t + 1, emb.shape[1] - 1)]
            next_valid[i] = False
    return {
        "x": np.where(np.isfinite(x), x, 0.0).astype(np.float32),
        "next_z": np.where(np.isfinite(next_z), next_z, 0.0).astype(np.float32),
        "next_valid": next_valid,
        "anchor_ep_t0": anchors,
        "episode": anchors[:, 0].astype(np.int64),
    }


class ResidualReEncoder(nn.Module):
    def __init__(self, dim: int) -> None:
        super().__init__()
        self.body = nn.Sequential(
            nn.LayerNorm(dim),
            nn.Linear(dim, 128),
            nn.GELU(),
            nn.Linear(128, dim),
        )
        self.pred = nn.Sequential(nn.LayerNorm(dim), nn.Linear(dim, 128), nn.GELU(), nn.Linear(128, dim))

    def forward(self, x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        z = x + 0.25 * self.body(x)
        pred_next = self.pred(z)
        return z, pred_next


class RawRanker(nn.Module):
    def __init__(self, dim: int) -> None:
        super().__init__()
        self.linear = nn.Linear(dim, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.linear(x).squeeze(-1)


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


def regression_tail_loss(score: torch.Tensor, target_log: torch.Tensor, tail_weight: torch.Tensor) -> torch.Tensor:
    s = score - torch.mean(score)
    y = (target_log - torch.mean(target_log)).detach()
    per = F.smooth_l1_loss(s, y, reduction="none")
    return (per * tail_weight).sum() / tail_weight.sum().clamp_min(1.0)


def tail_weights(cvar_tail: np.ndarray) -> np.ndarray:
    cut = float(np.percentile(cvar_tail.astype(np.float64), TAIL_Q))
    indicator = (cvar_tail >= cut).astype(np.float32)
    return (1.0 + CVAR_WEIGHT * indicator).astype(np.float32)


def train_reencoder(
    x_train: np.ndarray,
    next_train: np.ndarray,
    next_valid: np.ndarray,
    y_mean_h5: np.ndarray,
    cvar_tail: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> ResidualReEncoder:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = ResidualReEncoder(x_train.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    next_t = torch.from_numpy(next_train.astype(np.float32)).to(device)
    nv_t = torch.from_numpy(next_valid.astype(bool)).to(device)
    y_t = torch.from_numpy(y_mean_h5.astype(np.float32)).to(device)
    y_log_t = torch.from_numpy(np.log(y_mean_h5.astype(np.float64) + EPS).astype(np.float32)).to(device)
    ep_t = torch.from_numpy(episode.astype(np.int64)).to(device)
    tw_t = torch.from_numpy(tail_weights(cvar_tail)).to(device)
    generator = torch.Generator(device="cpu").manual_seed(seed + 1301)
    n = len(x_train)
    model.train()
    for epoch in range(EPOCHS):
        order = torch.randperm(n, generator=generator)
        for lo in range(0, n, BATCH):
            idx = order[lo : lo + BATCH].to(device)
            z, pred_next = model(x_t[idx])
            score = z[:, 0]
            rank_loss = pairwise_tail_rank_loss(score, y_t[idx], ep_t[idx], tw_t[idx])
            reg_loss = regression_tail_loss(score, y_log_t[idx], tw_t[idx])
            valid = nv_t[idx]
            pred_loss = (
                F.mse_loss(pred_next[valid], next_t[idx][valid])
                if bool(valid.any())
                else pred_next.sum() * 0.0
            )
            identity = F.mse_loss(z, x_t[idx])
            loss = (reg_loss if rank_loss is None else rank_loss + 0.15 * reg_loss) + 0.03 * pred_loss + 0.01 * identity
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite re-encoder loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
        if device.type == "cuda" and epoch in (24, 49, 74):
            torch.cuda.empty_cache()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


def train_raw_ranker(
    x_train: np.ndarray,
    y_mean_h5: np.ndarray,
    cvar_tail: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> RawRanker:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = RawRanker(x_train.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_mean_h5.astype(np.float32)).to(device)
    y_log_t = torch.from_numpy(np.log(y_mean_h5.astype(np.float64) + EPS).astype(np.float32)).to(device)
    ep_t = torch.from_numpy(episode.astype(np.int64)).to(device)
    tw_t = torch.from_numpy(tail_weights(cvar_tail)).to(device)
    generator = torch.Generator(device="cpu").manual_seed(seed + 2303)
    n = len(x_train)
    model.train()
    for _ in range(EPOCHS):
        order = torch.randperm(n, generator=generator)
        for lo in range(0, n, BATCH):
            idx = order[lo : lo + BATCH].to(device)
            score = model(x_t[idx])
            rank_loss = pairwise_tail_rank_loss(score, y_t[idx], ep_t[idx], tw_t[idx])
            reg_loss = regression_tail_loss(score, y_log_t[idx], tw_t[idx])
            loss = reg_loss if rank_loss is None else rank_loss + 0.15 * reg_loss
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite raw ranker loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


def reencoder_score(model: ResidualReEncoder, x: np.ndarray, device: torch.device) -> tuple[np.ndarray, np.ndarray]:
    score = np.zeros(len(x), dtype=np.float64)
    z_out = np.zeros_like(x, dtype=np.float32)
    with torch.inference_mode():
        for lo in range(0, len(x), 512):
            hi = min(lo + 512, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            z, _ = model(xb)
            z_out[lo:hi] = z.detach().cpu().numpy().astype(np.float32)
            score[lo:hi] = z[:, 0].detach().cpu().numpy().astype(np.float64)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return score, z_out


def raw_ranker_score(model: RawRanker, x: np.ndarray, device: torch.device) -> np.ndarray:
    out = np.zeros(len(x), dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, len(x), 512):
            hi = min(lo + 512, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            out[lo:hi] = model(xb).detach().cpu().numpy().astype(np.float64)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return out


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
    shaped: dict[str, Any],
    uniform: dict[str, Any],
    *,
    seed: int,
) -> dict[str, float]:
    a_err = shaped["episode_total_error"]
    b_err = uniform["episode_total_error"]
    a_steps = shaped["episode_emitted_steps"]
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
    if not vals:
        return {"observed": float("nan"), "low": float("nan"), "high": float("nan")}
    observed = float(np.mean(vals))
    rng = np.random.default_rng(seed)
    vals_np = np.asarray(vals, dtype=np.float64)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(vals_np), size=len(vals_np))
        samples[i] = float(vals_np[pick].mean())
    return {
        "observed": observed,
        "low": float(np.percentile(samples, 2.5)),
        "high": float(np.percentile(samples, 97.5)),
    }


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
        "measured_scope": ["allocation_delta", "auroc"],
        "reported_claim": f"fail-closed：{reason}；未报告 φ-latent allocation 改善。",
    }


def build_claim(
    phi_delta: dict[str, float],
    raw_delta: dict[str, float],
    rho: dict[str, float],
    phi_auroc: float,
    raw_auroc: float,
    verdict: str,
) -> str:
    if verdict == "positive":
        decision = "CI high<0，φ 表示塑造破了 allocation 天花板"
    elif verdict == "negative":
        decision = "CI low>=0，φ-latent 未优于 uniform，方向为负结论"
    else:
        decision = "CI 跨 0，不可识别为突破"
    if np.isfinite(rho["observed"]):
        rho_text = f"ρ={rho['observed']:.6f} [{rho['low']:.6f},{rho['high']:.6f}]"
    else:
        rho_text = "ρ=NA"
    return (
        f"φ-latent allocation_delta={phi_delta['observed']:.9g}, "
        f"95% CI=[{phi_delta['low']:.9g},{phi_delta['high']:.9g}]；{decision}。"
        f"raw-latent tail-ranker allocation_delta={raw_delta['observed']:.9g}, "
        f"95% CI=[{raw_delta['low']:.9g},{raw_delta['high']:.9g}]。"
        f"{rho_text}；φ h5/q75 AUROC={phi_auroc:.6f}, raw AUROC={raw_auroc:.6f}。"
        "φ 输入仅为 anchor LeWM latent；tail/CVaR 目标只在 train split 用于训练，eval 真值只用于最终度量。"
    )


def build_payload(seed: int) -> dict[str, Any]:
    device = configure_determinism(seed)
    if not LATENT_NPZ.exists() or not CLEAN_LABELS.exists():
        return make_fail_payload("缺少 tworooms latent 或 clean labels 输入")

    data = load_npz(LATENT_NPZ)
    labels = load_npz(CLEAN_LABELS)
    required = [
        "train_anchor_ep_t0",
        "train_valid",
        "train_err_at_h",
        "train_mean_err_to_h",
        "train_y",
        "eval_anchor_ep_t0",
        "eval_valid",
        "eval_err_at_h",
        "eval_mean_err_to_h",
        "eval_y",
    ]
    missing = [k for k in required if k not in labels]
    if missing:
        return make_fail_payload("clean labels 字段缺失：" + ",".join(missing))

    train_rows = build_latent_rows(data, labels, "train")
    eval_rows = build_latent_rows(data, labels, "eval")

    train_h5_valid = labels["train_valid"][:, TARGET_H_INDEX].astype(bool)
    eval_h5_valid = labels["eval_valid"][:, TARGET_H_INDEX].astype(bool)
    if int(train_h5_valid.sum()) == 0 or int(eval_h5_valid.sum()) == 0:
        return make_fail_payload("train/eval h=5 有效 anchor 为空")

    train_x_mean, train_x_scale = fit_standardizer(train_rows["x"])
    x_train_all = apply_standardizer(train_rows["x"], train_x_mean, train_x_scale)
    x_eval_all = apply_standardizer(eval_rows["x"], train_x_mean, train_x_scale)

    next_mean, next_scale = fit_standardizer(train_rows["next_z"][train_rows["next_valid"]])
    next_train_all = apply_standardizer(train_rows["next_z"], next_mean, next_scale)

    x_train = x_train_all[train_h5_valid]
    next_train = next_train_all[train_h5_valid]
    next_valid = train_rows["next_valid"][train_h5_valid]
    y_train = labels["train_mean_err_to_h"][train_h5_valid, TARGET_H_INDEX].astype(np.float64)
    cvar_train = np.max(labels["train_err_at_h"][train_h5_valid, :TARGET_H].astype(np.float64), axis=1)
    ep_train = train_rows["episode"][train_h5_valid].astype(np.int64)
    ep_eval = eval_rows["episode"][eval_h5_valid].astype(np.int64)
    if len(np.unique(ep_train)) < 2 or len(np.unique(ep_eval)) < 2:
        return make_fail_payload("episode split 过少，episode bootstrap 不可识别")
    if not np.isfinite(y_train).all() or float(np.std(y_train)) == 0.0:
        return make_fail_payload("train h=5 target 不可识别")

    phi = train_reencoder(
        x_train,
        next_train,
        next_valid,
        y_train,
        cvar_train,
        ep_train,
        seed=seed + 13,
        device=device,
    )
    raw_ranker = train_raw_ranker(
        x_train,
        y_train,
        cvar_train,
        ep_train,
        seed=seed + 29,
        device=device,
    )

    x_eval = x_eval_all[eval_h5_valid]
    phi_score, _ = reencoder_score(phi, x_eval, device)
    raw_score = raw_ranker_score(raw_ranker, x_eval, device)

    eval_anchors = eval_rows["anchor_ep_t0"][eval_h5_valid].astype(np.int64)
    errors_h5 = labels["eval_err_at_h"][eval_h5_valid, :TARGET_H].astype(np.float64)
    true_mean_h5 = labels["eval_mean_err_to_h"][eval_h5_valid, TARGET_H_INDEX].astype(np.float64)
    by_ep = anchors_by_episode(eval_anchors)
    uniform_alloc = summarize_allocation(allocation_uniform(by_ep), errors_h5, eval_anchors)
    phi_alloc = summarize_allocation(allocation_by_score(eval_anchors, by_ep, phi_score), errors_h5, eval_anchors)
    raw_alloc = summarize_allocation(allocation_by_score(eval_anchors, by_ep, raw_score), errors_h5, eval_anchors)
    phi_delta = paired_allocation_delta(phi_alloc, uniform_alloc, seed=seed + BOOTSTRAP_SEED_OFFSET)
    raw_delta = paired_allocation_delta(raw_alloc, uniform_alloc, seed=seed + BOOTSTRAP_SEED_OFFSET + 1)
    rho = bootstrap_spearman(phi_score, true_mean_h5, ep_eval, seed=seed + BOOTSTRAP_SEED_OFFSET + 2)

    y_eval_q75 = labels["eval_y"][eval_h5_valid, TARGET_H_INDEX, Q75_INDEX].astype(np.int8)
    phi_auroc = auroc_rank(y_eval_q75, phi_score)
    raw_auroc = auroc_rank(y_eval_q75, raw_score)

    verdict = verdict_from_delta(phi_delta["low"], phi_delta["high"])
    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": float(phi_delta["observed"]),
        "ci": {"low": float(phi_delta["low"]), "high": float(phi_delta["high"])},
    }
    if verdict == "unidentifiable":
        payload["status"] = "fail-closed"
    payload["measured_scope"] = ["allocation_delta", "auroc"]
    payload["reported_claim"] = build_claim(phi_delta, raw_delta, rho, phi_auroc, raw_auroc, verdict)
    if device.type == "cuda":
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
