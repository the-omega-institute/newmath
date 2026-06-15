#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import h5py
import hdf5plugin  # noqa: F401 - registers the Blosc HDF5 filter used by pixels.
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


HYPOTHESIS_ID = "derisk_alloc_a100"
METRIC = "allocation_delta"

TARGET_H = 5
TARGET_H_INDEX = TARGET_H - 1
Q75_INDEX = 1
UNIFORM_H = 3
LOW_H = 5
MID_H = 3
HIGH_H = 1
FRAMESKIP = 5

BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
EPS = 1.0e-8

IMAGE_SIZE = 64
BASE_LATENT_DIM = 64
ACTION_DIM = 2
BASE_BATCH = 512
BASE_EPOCHS = 160
LR = 5.0e-4
WEIGHT_DECAY = 5.0e-5
PRED_WEIGHT = 0.12
VAR_WEIGHT = 25.0
COV_WEIGHT = 4.0
TAIL_RANK_WEIGHT = 1.10
TAIL_REG_WEIGHT = 0.25
TAIL_Q = 75.0
CVAR_WEIGHT = 5.0

HEALTH_VAR_MEAN_MIN = 0.25
HEALTH_VAR_MIN_MIN = 1.0e-3
HEALTH_EFFECTIVE_RANK_MIN = 18.0

FIXED_LEWM_CEILING_TEXT = "fixed-LeWM ceiling: fi-012 about +0.005, fi-013 about +0.008"


def configure_determinism(seed: int) -> tuple[torch.device, bool, list[str]]:
    os.environ["PYTHONHASHSEED"] = str(seed)
    os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    relaxed_ops: list[str] = []
    deterministic = True
    try:
        torch.use_deterministic_algorithms(True)
    except RuntimeError as exc:
        torch.use_deterministic_algorithms(False)
        deterministic = False
        relaxed_ops.append(f"torch.use_deterministic_algorithms: {exc}")
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = deterministic
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
    return torch.device("cuda" if torch.cuda.is_available() else "cpu"), deterministic, relaxed_ops


def seed_all(seed: int) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


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


def bootstrap_spearman(score: np.ndarray, truth: np.ndarray, episode: np.ndarray, *, seed: int) -> dict[str, float]:
    by_ep = split_by_episode_indices(episode)
    vals: list[float] = []
    for idx in by_ep:
        rho = spearman_one(score[idx], truth[idx])
        if np.isfinite(rho):
            vals.append(float(rho))
    if not vals:
        return {"observed": float("nan"), "low": float("nan"), "high": float("nan")}
    vals_np = np.asarray(vals, dtype=np.float64)
    observed = float(vals_np.mean())
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(vals_np), size=len(vals_np))
        samples[i] = float(vals_np[pick].mean())
    return {
        "observed": observed,
        "low": float(np.percentile(samples, 2.5)),
        "high": float(np.percentile(samples, 97.5)),
    }


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


def paired_allocation_delta(shaped: dict[str, Any], uniform: dict[str, Any], *, seed: int) -> dict[str, float]:
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


def verdict_from_delta(ci_low: float, ci_high: float) -> str:
    if ci_high < 0.0:
        return "positive"
    if ci_low >= 0.0:
        return "negative"
    return "fail-closed"


def h5_frame_indices(anchors: np.ndarray, ep_offset: np.ndarray, ep_len: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    current = np.zeros(len(anchors), dtype=np.int64)
    next_frame = np.zeros(len(anchors), dtype=np.int64)
    valid_next = np.zeros(len(anchors), dtype=bool)
    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t = int(t_raw)
        cur_step = int(t * FRAMESKIP)
        nxt_step = int((t + 1) * FRAMESKIP)
        off = int(ep_offset[ep])
        length = int(ep_len[ep])
        if cur_step >= length:
            raise RuntimeError(f"anchor maps outside HDF5 episode: ep={ep} t={t}")
        current[i] = off + cur_step
        if nxt_step < length:
            next_frame[i] = off + nxt_step
            valid_next[i] = True
        else:
            next_frame[i] = off + cur_step
            valid_next[i] = False
    return current, next_frame, valid_next


def preprocess_pixels_np(pixels: np.ndarray) -> np.ndarray:
    x = torch.from_numpy(pixels.astype(np.float32)).permute(0, 3, 1, 2) / 255.0
    x = F.interpolate(x, size=(IMAGE_SIZE, IMAGE_SIZE), mode="bilinear", align_corners=False)
    return x.numpy().astype(np.float32)


def materialize_pixels(h5_path: Path, frame_indices: np.ndarray, *, batch: int = 128) -> np.ndarray:
    frame_indices = frame_indices.astype(np.int64)
    unique, inverse = np.unique(frame_indices, return_inverse=True)
    unique_pixels = np.zeros((len(unique), 3, IMAGE_SIZE, IMAGE_SIZE), dtype=np.float32)
    with h5py.File(h5_path, "r") as h5:
        pix = h5["pixels"]
        for lo in range(0, len(unique), batch):
            hi = min(lo + batch, len(unique))
            raw = np.asarray(pix[unique[lo:hi]])
            unique_pixels[lo:hi] = preprocess_pixels_np(raw)
    return unique_pixels[inverse].astype(np.float32, copy=False)


def materialize_actions(h5_path: Path, frame_indices: np.ndarray) -> np.ndarray:
    frame_indices = frame_indices.astype(np.int64)
    unique, inverse = np.unique(frame_indices, return_inverse=True)
    with h5py.File(h5_path, "r") as h5:
        unique_actions = np.asarray(h5["action"][unique], dtype=np.float32)
    return unique_actions[inverse].astype(np.float32, copy=False)


class NativePixelRows(torch.utils.data.Dataset[tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]]):
    def __init__(
        self,
        *,
        current_pixels: np.ndarray,
        next_pixels: np.ndarray,
        actions: np.ndarray,
        y_mean: np.ndarray,
        y_log: np.ndarray,
        episode: np.ndarray,
        tail_weight: np.ndarray,
    ) -> None:
        self.current_pixels = current_pixels.astype(np.float32, copy=False)
        self.next_pixels = next_pixels.astype(np.float32, copy=False)
        self.actions = actions.astype(np.float32, copy=False)
        self.y_mean = y_mean.astype(np.float32)
        self.y_log = y_log.astype(np.float32)
        self.episode = episode.astype(np.int64)
        self.tail_weight = tail_weight.astype(np.float32)

    def __len__(self) -> int:
        return int(len(self.current_pixels))

    def __getitem__(
        self, index: int
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        cur = torch.from_numpy(self.current_pixels[index])
        nxt = torch.from_numpy(self.next_pixels[index])
        action = torch.from_numpy(self.actions[index])
        y = torch.tensor(float(self.y_mean[index]), dtype=torch.float32)
        ylog = torch.tensor(float(self.y_log[index]), dtype=torch.float32)
        ep = torch.tensor(int(self.episode[index]), dtype=torch.int64)
        tw = torch.tensor(float(self.tail_weight[index]), dtype=torch.float32)
        return cur, nxt, action, y, ylog, ep, tw


class ResidualBlock(nn.Module):
    def __init__(self, channels: int, groups: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Conv2d(channels, channels, kernel_size=3, padding=1),
            nn.GroupNorm(groups, channels),
            nn.GELU(),
            nn.Conv2d(channels, channels, kernel_size=3, padding=1),
            nn.GroupNorm(groups, channels),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return F.gelu(x + self.net(x))


def group_count(channels: int) -> int:
    for groups in (32, 16, 8, 5, 4, 2, 1):
        if channels % groups == 0:
            return groups
    return 1


class PixelEncoder(nn.Module):
    def __init__(self, latent_dim: int, *, width_mult: int, depth_mult: int) -> None:
        super().__init__()
        c1 = 24 * width_mult
        c2 = 40 * width_mult
        c3 = 64 * width_mult
        c4 = 96 * width_mult
        layers: list[nn.Module] = [
            nn.Conv2d(3, c1, kernel_size=5, stride=2, padding=2),
            nn.GroupNorm(group_count(c1), c1),
            nn.GELU(),
            nn.Conv2d(c1, c2, kernel_size=3, stride=2, padding=1),
            nn.GroupNorm(group_count(c2), c2),
            nn.GELU(),
        ]
        for _ in range(max(0, depth_mult - 1)):
            layers.append(ResidualBlock(c2, group_count(c2)))
        layers.extend(
            [
                nn.Conv2d(c2, c3, kernel_size=3, stride=2, padding=1),
                nn.GroupNorm(group_count(c3), c3),
                nn.GELU(),
            ]
        )
        for _ in range(max(0, depth_mult - 1)):
            layers.append(ResidualBlock(c3, group_count(c3)))
        layers.extend(
            [
                nn.Conv2d(c3, c4, kernel_size=3, stride=2, padding=1),
                nn.GroupNorm(group_count(c4), c4),
                nn.GELU(),
            ]
        )
        for _ in range(max(0, depth_mult - 1)):
            layers.append(ResidualBlock(c4, group_count(c4)))
        layers.append(nn.AdaptiveAvgPool2d((1, 1)))
        hidden = max(128 * width_mult, latent_dim)
        self.conv = nn.Sequential(*layers)
        self.proj = nn.Sequential(
            nn.Flatten(),
            nn.Linear(c4, hidden),
            nn.LayerNorm(hidden),
            nn.GELU(),
            nn.Linear(hidden, latent_dim),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.proj(self.conv(x))


class NativeEncoderModel(nn.Module):
    def __init__(self, *, latent_dim: int, width_mult: int, depth_mult: int) -> None:
        super().__init__()
        action_hidden = 32 * width_mult
        pred_hidden = max(128 * width_mult, latent_dim * 2)
        tail_hidden = max(64 * width_mult, latent_dim)
        self.latent_dim = latent_dim
        self.encoder = PixelEncoder(latent_dim, width_mult=width_mult, depth_mult=depth_mult)
        self.action_encoder = nn.Sequential(
            nn.Linear(ACTION_DIM, action_hidden),
            nn.GELU(),
            nn.Linear(action_hidden, action_hidden),
        )
        self.predictor = nn.Sequential(
            nn.Linear(latent_dim + action_hidden, pred_hidden),
            nn.LayerNorm(pred_hidden),
            nn.GELU(),
            nn.Linear(pred_hidden, latent_dim),
        )
        self.tail_head = nn.Sequential(
            nn.LayerNorm(latent_dim),
            nn.Linear(latent_dim, tail_hidden),
            nn.GELU(),
            nn.Linear(tail_hidden, 1),
        )

    def encode(self, x: torch.Tensor) -> torch.Tensor:
        return self.encoder(x)

    def forward(self, x: torch.Tensor, action: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        z = self.encoder(x)
        a = self.action_encoder(action)
        pred = self.predictor(torch.cat([z, a], dim=1))
        score = self.tail_head(z).squeeze(-1)
        return z, pred, score


def init_native_model(model: nn.Module) -> None:
    for module in model.modules():
        if isinstance(module, (nn.Conv2d, nn.Linear)):
            nn.init.kaiming_uniform_(module.weight, a=math.sqrt(5.0))
            if module.bias is not None:
                fan_in, _ = nn.init._calculate_fan_in_and_fan_out(module.weight)
                bound = 1.0 / math.sqrt(fan_in) if fan_in > 0 else 0.0
                nn.init.uniform_(module.bias, -bound, bound)


def variance_loss(z: torch.Tensor) -> torch.Tensor:
    if z.shape[0] < 2:
        return z.sum() * 0.0
    std = torch.sqrt(z.var(dim=0, unbiased=False) + EPS)
    return torch.mean(F.relu(1.0 - std).pow(2))


def covariance_loss(z: torch.Tensor) -> torch.Tensor:
    n, d = z.shape
    if n < 2 or d < 2:
        return z.sum() * 0.0
    centered = z - z.mean(dim=0)
    cov = centered.T @ centered / float(n - 1)
    std = torch.sqrt(torch.diag(cov).clamp_min(EPS))
    corr = cov / (std[:, None] * std[None, :]).clamp_min(EPS)
    off = corr - torch.diag(torch.diag(corr))
    return off.pow(2).sum() / float(d)


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


def train_native_encoder(
    dataset: NativePixelRows,
    *,
    seed: int,
    device: torch.device,
    width_mult: int,
    depth_mult: int,
    latent_dim: int,
    batch: int,
    epochs: int,
    amp: bool,
    lr: float,
    var_weight: float,
    cov_weight: float,
    warmup_frac: float,
) -> NativeEncoderModel:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = NativeEncoderModel(latent_dim=latent_dim, width_mult=width_mult, depth_mult=depth_mult).to(device)
    init_native_model(model)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=WEIGHT_DECAY)
    generator = torch.Generator(device="cpu").manual_seed(seed + 4703)
    loader = torch.utils.data.DataLoader(
        dataset,
        batch_size=batch,
        shuffle=True,
        generator=generator,
        num_workers=0,
        drop_last=True,
        pin_memory=(device.type == "cuda"),
    )
    scaler = torch.cuda.amp.GradScaler(enabled=amp and device.type == "cuda")
    model.train()
    total_steps = epochs * len(loader)
    warmup_steps = int(warmup_frac * total_steps)
    global_step = 0
    for epoch in range(epochs):
        for cur, nxt, action, y, ylog, ep, tw in loader:
            cur = cur.to(device, non_blocking=(device.type == "cuda"))
            nxt = nxt.to(device, non_blocking=(device.type == "cuda"))
            action = action.to(device, non_blocking=(device.type == "cuda"))
            y = y.to(device, non_blocking=(device.type == "cuda"))
            ylog = ylog.to(device, non_blocking=(device.type == "cuda"))
            ep = ep.to(device, non_blocking=(device.type == "cuda"))
            tw = tw.to(device, non_blocking=(device.type == "cuda"))
            if warmup_steps > 0:
                lr_t = lr * min(1.0, global_step / warmup_steps)
                for group in opt.param_groups:
                    group["lr"] = lr_t
            opt.zero_grad(set_to_none=True)
            with torch.cuda.amp.autocast(enabled=amp and device.type == "cuda"):
                z, pred_next, score = model(cur, action)
                z_next = model.encode(nxt)
                pred_loss = F.smooth_l1_loss(pred_next, z_next.detach())
                var_reg = 0.5 * (variance_loss(z) + variance_loss(z_next))
                cov_reg = 0.5 * (covariance_loss(z) + covariance_loss(z_next))
                rank_loss = pairwise_tail_rank_loss(score, y, ep, tw)
                reg_loss = regression_tail_loss(score, ylog, tw)
                tail_loss = reg_loss if rank_loss is None else rank_loss + TAIL_REG_WEIGHT * reg_loss
                loss = PRED_WEIGHT * pred_loss + var_weight * var_reg + cov_weight * cov_reg + TAIL_RANK_WEIGHT * tail_loss
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite native encoder loss")
            scaler.scale(loss).backward()
            scaler.unscale_(opt)
            torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=5.0)
            scaler.step(opt)
            scaler.update()
            global_step += 1
        if device.type == "cuda" and epoch in {epochs // 4, epochs // 2, (3 * epochs) // 4}:
            torch.cuda.empty_cache()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


def score_rows(
    model: NativeEncoderModel,
    *,
    pixels: np.ndarray,
    device: torch.device,
    latent_dim: int,
) -> tuple[np.ndarray, np.ndarray]:
    score = np.zeros(len(pixels), dtype=np.float64)
    latents = np.zeros((len(pixels), latent_dim), dtype=np.float32)
    with torch.inference_mode():
        for lo in range(0, len(pixels), 256):
            hi = min(lo + 256, len(pixels))
            xb = torch.from_numpy(pixels[lo:hi].astype(np.float32, copy=False)).to(
                device, non_blocking=(device.type == "cuda")
            )
            z = model.encode(xb)
            s = model.tail_head(z).squeeze(-1)
            latents[lo:hi] = z.detach().cpu().numpy().astype(np.float32)
            score[lo:hi] = s.detach().cpu().numpy().astype(np.float64)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return score, latents


def representation_stats(z: np.ndarray) -> dict[str, float]:
    var = np.var(z.astype(np.float64), axis=0)
    cov = np.cov(z.astype(np.float64), rowvar=False)
    eig = np.linalg.eigvalsh(cov)
    eig = np.clip(eig, 0.0, None)
    total = float(eig.sum())
    if total <= 0.0:
        eff_rank = 0.0
    else:
        p = eig / total
        p = p[p > 0.0]
        eff_rank = float(np.exp(-np.sum(p * np.log(p))))
    return {
        "var_mean": float(var.mean()),
        "var_min": float(var.min()),
        "effective_rank": eff_rank,
    }


def health_verdict(stats: dict[str, float]) -> tuple[bool, str]:
    ok = (
        stats["var_mean"] >= HEALTH_VAR_MEAN_MIN
        and stats["var_min"] >= HEALTH_VAR_MIN_MIN
        and stats["effective_rank"] >= HEALTH_EFFECTIVE_RANK_MIN
    )
    reason = (
        f"var_mean={stats['var_mean']:.6g}, var_min={stats['var_min']:.6g}, "
        f"effective_rank={stats['effective_rank']:.6g}, thresholds "
        f"var_mean>={HEALTH_VAR_MEAN_MIN:g}, var_min>={HEALTH_VAR_MIN_MIN:g}, "
        f"effective_rank>={HEALTH_EFFECTIVE_RANK_MIN:g}"
    )
    return ok, reason


def count_params(model: nn.Module) -> int:
    return int(sum(p.numel() for p in model.parameters()))


def make_fail_payload(
    *,
    reason: str,
    width_mult: int,
    depth_mult: int,
    latent_dim: int,
    batch: int,
    epochs: int,
    lr: float,
    var_weight: float,
    cov_weight: float,
    warmup_frac: float,
    params_count: int,
    device: str,
    wall_time_sec: float,
    deterministic: bool,
    relaxed_ops: list[str],
) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "width_mult": width_mult,
        "depth_mult": depth_mult,
        "latent_dim": latent_dim,
        "batch": batch,
        "epochs": epochs,
        "lr": float(lr),
        "var_weight": float(var_weight),
        "cov_weight": float(cov_weight),
        "warmup_frac": float(warmup_frac),
        "params_count": params_count,
        "metric": METRIC,
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "rho": {"observed": 0.0, "low": 0.0, "high": 0.0},
        "auroc": 0.5,
        "health": {"var_mean": 0.0, "var_min": 0.0, "effective_rank": 0.0, "healthy": False},
        "status": "fail-closed",
        "device": device,
        "wall_time_sec": float(wall_time_sec),
        "deterministic": bool(deterministic),
        "determinism_relaxed_ops": relaxed_ops,
        "reported_claim": (
            f"scale width_mult={width_mult}, depth_mult={depth_mult}, latent_dim={latent_dim}, "
            f"batch={batch}, epochs={epochs}, lr={lr:g}, var_weight={var_weight:g}, "
            f"cov_weight={cov_weight:g}, warmup_frac={warmup_frac:g}: "
            f"fail-closed before allocation metric; {reason}. "
            "rho did not pass 0.5 and allocation was not reported."
        ),
    }


def build_claim(
    *,
    width_mult: int,
    depth_mult: int,
    latent_dim: int,
    batch: int,
    epochs: int,
    lr: float,
    var_weight: float,
    cov_weight: float,
    warmup_frac: float,
    delta: dict[str, float],
    rho: dict[str, float],
    auroc: float,
    stats: dict[str, float],
    verdict: str,
    device: torch.device,
    deterministic: bool,
) -> str:
    rho_ok = bool(np.isfinite(rho["observed"]) and rho["observed"] > 0.5)
    alloc_broke = verdict == "positive"
    if alloc_broke:
        decision = "allocation_delta CI high<0, allocation breaks uniform baseline"
    elif verdict == "negative":
        decision = "allocation_delta CI low>=0, allocation remains on the wrong side"
    else:
        decision = "allocation_delta CI crosses 0, allocation result is fail-closed"
    return (
        f"scale width_mult={width_mult}, depth_mult={depth_mult}, latent_dim={latent_dim}, "
        f"batch={batch}, epochs={epochs}, lr={lr:g}, var_weight={var_weight:g}, "
        f"cov_weight={cov_weight:g}, warmup_frac={warmup_frac:g}: rho={rho['observed']:.6f} "
        f"[{rho['low']:.6f},{rho['high']:.6f}], rho_over_0.5={rho_ok}; "
        f"allocation_delta={delta['observed']:.9g}, 95% CI=[{delta['low']:.9g},{delta['high']:.9g}], "
        f"allocation_broke={alloc_broke}; {decision}. h5/q75 AUROC={auroc:.6f}. "
        f"health var_mean={stats['var_mean']:.6g}, var_min={stats['var_min']:.6g}, "
        f"effective_rank={stats['effective_rank']:.6g}. "
        f"{FIXED_LEWM_CEILING_TEXT}. Encoder saw pixels/actions only; allocation targets were train-split losses only, "
        f"eval truth used only after the health gate for final metrics; train/eval episodes isolated. "
        f"device={device.type}, deterministic={deterministic}."
    )


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    t0 = time.perf_counter()
    width_mult = int(args.width_mult)
    depth_mult = int(args.depth_mult)
    latent_dim = int(args.latent_dim)
    batch = int(args.batch)
    epochs = int(args.epochs)
    lr = float(args.lr)
    var_weight = float(args.var_weight)
    cov_weight = float(args.cov_weight)
    warmup_frac = float(args.warmup_frac)
    h5_path = Path(args.h5)
    labels_path = Path(args.labels)
    device, deterministic, relaxed_ops = configure_determinism(int(args.seed))
    params_count = count_params(
        NativeEncoderModel(latent_dim=latent_dim, width_mult=width_mult, depth_mult=depth_mult)
    )
    fail_kwargs = {
        "width_mult": width_mult,
        "depth_mult": depth_mult,
        "latent_dim": latent_dim,
        "batch": batch,
        "epochs": epochs,
        "lr": lr,
        "var_weight": var_weight,
        "cov_weight": cov_weight,
        "warmup_frac": warmup_frac,
        "params_count": params_count,
        "device": device.type,
        "deterministic": deterministic,
        "relaxed_ops": relaxed_ops,
    }
    if not h5_path.exists() or not labels_path.exists():
        return make_fail_payload(
            reason=f"missing h5 or labels path: h5={h5_path}, labels={labels_path}",
            wall_time_sec=time.perf_counter() - t0,
            **fail_kwargs,
        )
    labels = load_npz(labels_path)
    required = [
        "train_anchor_ep_t0",
        "train_valid",
        "train_err_at_h",
        "train_mean_err_to_h",
        "eval_anchor_ep_t0",
        "eval_valid",
        "eval_err_at_h",
        "eval_mean_err_to_h",
        "eval_y",
    ]
    missing = [k for k in required if k not in labels]
    if missing:
        return make_fail_payload(
            reason="missing label fields: " + ",".join(missing),
            wall_time_sec=time.perf_counter() - t0,
            **fail_kwargs,
        )

    with h5py.File(h5_path, "r") as h5:
        ep_offset = np.asarray(h5["ep_offset"], dtype=np.int64)
        ep_len = np.asarray(h5["ep_len"], dtype=np.int64)

    train_valid = labels["train_valid"][:, TARGET_H_INDEX].astype(bool)
    eval_valid = labels["eval_valid"][:, TARGET_H_INDEX].astype(bool)
    if int(train_valid.sum()) == 0 or int(eval_valid.sum()) == 0:
        return make_fail_payload(
            reason="empty h=5 train/eval anchors",
            wall_time_sec=time.perf_counter() - t0,
            **fail_kwargs,
        )

    train_anchors = labels["train_anchor_ep_t0"][train_valid].astype(np.int64)
    eval_anchors = labels["eval_anchor_ep_t0"][eval_valid].astype(np.int64)
    train_current, train_next, train_next_valid = h5_frame_indices(train_anchors, ep_offset, ep_len)
    eval_current, _eval_next, _eval_next_valid = h5_frame_indices(eval_anchors, ep_offset, ep_len)
    train_current = train_current[train_next_valid]
    train_next = train_next[train_next_valid]
    train_anchors_for_data = train_anchors[train_next_valid]

    y_train_all = labels["train_mean_err_to_h"][train_valid, TARGET_H_INDEX].astype(np.float64)
    err_train_all = labels["train_err_at_h"][train_valid, :TARGET_H].astype(np.float64)
    y_train = y_train_all[train_next_valid]
    cvar_train = np.max(err_train_all[train_next_valid], axis=1)
    if len(np.unique(train_anchors_for_data[:, 0])) < 2 or len(np.unique(eval_anchors[:, 0])) < 2:
        return make_fail_payload(
            reason="too few episodes for episode bootstrap",
            wall_time_sec=time.perf_counter() - t0,
            **fail_kwargs,
        )
    if not np.isfinite(y_train).all() or float(np.std(y_train)) == 0.0:
        return make_fail_payload(
            reason="train h=5 target is not identifiable",
            wall_time_sec=time.perf_counter() - t0,
            **fail_kwargs,
        )

    train_current_pixels = materialize_pixels(h5_path, train_current)
    train_next_pixels = materialize_pixels(h5_path, train_next)
    train_actions = materialize_actions(h5_path, train_current)
    eval_pixels = materialize_pixels(h5_path, eval_current)

    train_dataset = NativePixelRows(
        current_pixels=train_current_pixels,
        next_pixels=train_next_pixels,
        actions=train_actions,
        y_mean=y_train,
        y_log=np.log(y_train + EPS).astype(np.float32),
        episode=train_anchors_for_data[:, 0].astype(np.int64),
        tail_weight=tail_weights(cvar_train),
    )
    train_seed = int(args.seed) + 1409
    try:
        model = train_native_encoder(
            train_dataset,
            seed=train_seed,
            device=device,
            width_mult=width_mult,
            depth_mult=depth_mult,
            latent_dim=latent_dim,
            batch=batch,
            epochs=epochs,
            amp=bool(int(args.amp)),
            lr=lr,
            var_weight=var_weight,
            cov_weight=cov_weight,
            warmup_frac=warmup_frac,
        )
    except RuntimeError as exc:
        message = str(exc)
        deterministic_error = "deterministic" in message.lower() or "CUBLAS_WORKSPACE_CONFIG" in message
        if not deterministic_error:
            raise
        deterministic = False
        relaxed_ops.append("training_runtime_determinism: " + message.splitlines()[0][:240])
        torch.use_deterministic_algorithms(False)
        torch.backends.cudnn.deterministic = False
        if device.type == "cuda":
            torch.cuda.empty_cache()
        seed_all(train_seed)
        model = train_native_encoder(
            train_dataset,
            seed=train_seed,
            device=device,
            width_mult=width_mult,
            depth_mult=depth_mult,
            latent_dim=latent_dim,
            batch=batch,
            epochs=epochs,
            amp=bool(int(args.amp)),
            lr=lr,
            var_weight=var_weight,
            cov_weight=cov_weight,
            warmup_frac=warmup_frac,
        )
        fail_kwargs["deterministic"] = deterministic

    eval_score, eval_latents = score_rows(model, pixels=eval_pixels, device=device, latent_dim=latent_dim)
    stats = representation_stats(eval_latents)
    healthy, health_reason = health_verdict(stats)
    if not healthy:
        if device.type == "cuda":
            torch.cuda.empty_cache()
        payload = make_fail_payload(
            reason="latent still collapsed or under-rank after VICReg; " + health_reason,
            wall_time_sec=time.perf_counter() - t0,
            **fail_kwargs,
        )
        payload["health"] = {
            "var_mean": float(stats["var_mean"]),
            "var_min": float(stats["var_min"]),
            "effective_rank": float(stats["effective_rank"]),
            "healthy": False,
        }
        return payload

    eval_errors_h5 = labels["eval_err_at_h"][eval_valid, :TARGET_H].astype(np.float64)
    true_mean_h5 = labels["eval_mean_err_to_h"][eval_valid, TARGET_H_INDEX].astype(np.float64)
    ep_eval = eval_anchors[:, 0].astype(np.int64)

    by_ep = anchors_by_episode(eval_anchors)
    uniform_alloc = summarize_allocation(allocation_uniform(by_ep), eval_errors_h5, eval_anchors)
    native_alloc = summarize_allocation(allocation_by_score(eval_anchors, by_ep, eval_score), eval_errors_h5, eval_anchors)
    delta = paired_allocation_delta(native_alloc, uniform_alloc, seed=int(args.seed) + BOOTSTRAP_SEED_OFFSET)
    rho = bootstrap_spearman(eval_score, true_mean_h5, ep_eval, seed=int(args.seed) + BOOTSTRAP_SEED_OFFSET + 1)
    y_eval_q75 = labels["eval_y"][eval_valid, TARGET_H_INDEX, Q75_INDEX].astype(np.int8)
    auroc = auroc_rank(y_eval_q75, eval_score)
    verdict = verdict_from_delta(delta["low"], delta["high"])
    wall_time_sec = time.perf_counter() - t0

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "width_mult": width_mult,
        "depth_mult": depth_mult,
        "latent_dim": latent_dim,
        "batch": batch,
        "epochs": epochs,
        "lr": float(lr),
        "var_weight": float(var_weight),
        "cov_weight": float(cov_weight),
        "warmup_frac": float(warmup_frac),
        "params_count": params_count,
        "metric": METRIC,
        "metric_value": float(delta["observed"]),
        "ci": {"low": float(delta["low"]), "high": float(delta["high"])},
        "rho": {"observed": float(rho["observed"]), "low": float(rho["low"]), "high": float(rho["high"])},
        "auroc": float(auroc),
        "health": {
            "var_mean": float(stats["var_mean"]),
            "var_min": float(stats["var_min"]),
            "effective_rank": float(stats["effective_rank"]),
            "healthy": True,
        },
        "status": verdict,
        "device": device.type,
        "wall_time_sec": float(wall_time_sec),
        "deterministic": bool(deterministic),
        "determinism_relaxed_ops": relaxed_ops,
    }
    payload["reported_claim"] = build_claim(
        width_mult=width_mult,
        depth_mult=depth_mult,
        latent_dim=latent_dim,
        batch=batch,
        epochs=epochs,
        lr=lr,
        var_weight=var_weight,
        cov_weight=cov_weight,
        warmup_frac=warmup_frac,
        delta=delta,
        rho=rho,
        auroc=auroc,
        stats=stats,
        verdict=verdict,
        device=device,
        deterministic=deterministic,
    )
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return payload


def positive_int(value: str) -> int:
    out = int(value)
    if out <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return out


def nonnegative_float(value: str) -> float:
    out = float(value)
    if not math.isfinite(out) or out < 0.0:
        raise argparse.ArgumentTypeError("must be finite and non-negative")
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--h5", required=True)
    parser.add_argument("--labels", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--width-mult", type=positive_int, default=1)
    parser.add_argument("--depth-mult", type=positive_int, default=1)
    parser.add_argument("--latent-dim", type=positive_int, default=BASE_LATENT_DIM)
    parser.add_argument("--batch", type=positive_int, default=BASE_BATCH)
    parser.add_argument("--epochs", type=positive_int, default=BASE_EPOCHS)
    parser.add_argument("--amp", type=int, choices=(0, 1), default=0)
    parser.add_argument("--lr", type=nonnegative_float, default=LR)
    parser.add_argument("--var-weight", type=nonnegative_float, default=VAR_WEIGHT)
    parser.add_argument("--cov-weight", type=nonnegative_float, default=COV_WEIGHT)
    parser.add_argument("--warmup-frac", type=nonnegative_float, default=0.0)
    args = parser.parse_args()

    payload = clean_json(build_payload(args))
    claim = str(payload.get("reported_claim", ""))
    forbidden = ("real_robot" + "_transfer", "paper_claim" + "_strength")
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
