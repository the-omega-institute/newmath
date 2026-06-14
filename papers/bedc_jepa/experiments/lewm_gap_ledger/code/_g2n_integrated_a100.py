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
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_LATENTS = ROOT / "tworooms_latent_large.npz"
DEFAULT_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
DEFAULT_OUT = REPORT_DIR / "g2n_integrated_a100_local.json"

TARGET_HORIZONS = (1, 3, 5, 10)
Q75 = 75
WINDOW_BACK = 4
MAX_ACTION_H = 10
ALLOC_H = 5
UNIFORM_H = 3
LOW_H = 5
MID_H = 3
HIGH_H = 1
ALPHA = 0.10
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
EPS = 1.0e-8
STRONGEST_POSTHOC_H1_AUROC = 0.744  # Phase1c logistic gap head strongest post-hoc probe.
MAX_CONSECUTIVE_NONFINITE_EPOCHS = 3

WEIGHT_DECAY = 1.0e-4
TAIL_Q = 75.0
TAIL_CVAR_WEIGHT = 5.0
TAIL_REG_WEIGHT = 0.15
PRED_WEIGHT = 0.20
TAIL_WEIGHT = 1.0
OOD_WEIGHT = 0.25
ADMISSION_WEIGHT = 0.25

FORBIDDEN_CLAIM_TOKENS = (
    "real" + "_robot" + "_transfer",
    "paper" + "_claim" + "_strength",
)


def configure_determinism(seed: int) -> tuple[torch.device, dict[str, Any]]:
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
        relaxed_ops.append(f"torch.use_deterministic_algorithms: {str(exc).splitlines()[0][:240]}")
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
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    return device, {
        "seed": int(seed),
        "torch_deterministic_algorithms": bool(deterministic),
        "cublas_workspace_config": os.environ.get("CUBLAS_WORKSPACE_CONFIG", ""),
        "cudnn_benchmark": bool(torch.backends.cudnn.benchmark),
        "cudnn_deterministic": bool(torch.backends.cudnn.deterministic),
        "tf32_matmul": bool(torch.backends.cuda.matmul.allow_tf32),
        "tf32_cudnn": bool(torch.backends.cudnn.allow_tf32),
        "device": device.type,
        "relaxed_ops": relaxed_ops,
    }


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite float for JSON payload: {out!r}")
    return out


def safe_tensor_scalar(value: torch.Tensor) -> float:
    out = float(value.detach().cpu())
    return out if math.isfinite(out) else 0.0


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
        return {key: raw[key] for key in raw.files}


def positive_int(value: str) -> int:
    out = int(value)
    if out <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return out


def nonnegative_int(value: str) -> int:
    out = int(value)
    if out < 0:
        raise argparse.ArgumentTypeError("must be non-negative")
    return out


def finite_float(value: str) -> float:
    out = float(value)
    if not math.isfinite(out):
        raise argparse.ArgumentTypeError("must be finite")
    return out


def zero_one(value: str) -> int:
    out = int(value)
    if out not in (0, 1):
        raise argparse.ArgumentTypeError("must be 0 or 1")
    return out


def horizon_indices(labels: dict[str, np.ndarray]) -> dict[int, int]:
    horizons = [int(x) for x in labels["horizons"].reshape(-1)]
    missing = [h for h in TARGET_HORIZONS if h not in horizons]
    if missing:
        raise RuntimeError(f"missing required horizons: {missing}")
    return {h: horizons.index(h) for h in TARGET_HORIZONS}


def q75_index(labels: dict[str, np.ndarray]) -> int:
    quantiles = [int(x) for x in labels["quantiles"].reshape(-1)]
    if Q75 not in quantiles:
        raise RuntimeError("missing q75 label")
    return int(quantiles.index(Q75))


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x - mean) / scale).astype(np.float32)


def safe_norm(x: np.ndarray, axis: int) -> np.ndarray:
    return np.linalg.norm(np.where(np.isfinite(x), x, 0.0), axis=axis).astype(np.float32)


def build_features(
    latents: dict[str, np.ndarray],
    labels: dict[str, np.ndarray],
    split: str,
    *,
    use_rollout: bool,
) -> dict[str, np.ndarray]:
    anchors = labels[f"{split}_anchor_ep_t0"].astype(np.int64)
    emb = latents["emb"].astype(np.float32)
    action = latents["action"].astype(np.float32)
    pred = latents.get("pred")
    pred_np = pred.astype(np.float32) if pred is not None else None
    selected_len = latents.get("selected_ep_len")
    ep_len = selected_len.astype(np.int64) if selected_len is not None else np.full(emb.shape[0], emb.shape[1], dtype=np.int64)
    pred_z = labels[f"{split}_pred_z"].astype(np.float32)
    valid = labels[f"{split}_valid"].astype(bool)

    n = int(len(anchors))
    z_dim = int(emb.shape[-1])
    a_dim = int(action.shape[-1])
    window_len = WINDOW_BACK + 1
    z_window = np.zeros((n, window_len, z_dim), dtype=np.float32)
    a_future = np.zeros((n, MAX_ACTION_H, a_dim), dtype=np.float32)
    a_valid = np.zeros((n, MAX_ACTION_H), dtype=np.float32)
    t_features = np.zeros((n, 2), dtype=np.float32)
    current_z = np.zeros((n, z_dim), dtype=np.float32)

    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t = int(t_raw)
        limit = int(min(max(ep_len[ep], 1), emb.shape[1]))
        current_t = min(max(t, 0), limit - 1)
        current_z[i] = emb[ep, current_t]
        denom = float(max(1, limit - 1))
        t_features[i, 0] = float(current_t) / denom
        t_features[i, 1] = float(limit) / float(max(1, emb.shape[1]))

        for w in range(window_len):
            src = max(0, current_t - WINDOW_BACK + w)
            src = min(src, limit - 1)
            z_window[i, w] = emb[ep, src]
        for h in range(MAX_ACTION_H):
            src = current_t + h
            if src < action.shape[1] and src < limit:
                a_future[i, h] = action[ep, src]
                a_valid[i, h] = 1.0

    pieces = [
        z_window.reshape(n, -1),
        a_future.reshape(n, -1),
        a_valid,
        t_features,
    ]

    audit_feature_groups = ["latent_window_z_t_minus_4_to_t", "future_action_sequence_t_to_t_plus_9"]
    if use_rollout:
        rollout = pred_z[:, :MAX_ACTION_H].copy()
        rollout_valid = valid[:, :MAX_ACTION_H].astype(np.float32)
        rollout[~valid[:, :MAX_ACTION_H]] = 0.0
        previous = np.concatenate([current_z[:, None, :], rollout[:, :-1, :]], axis=1)
        delta = (rollout - previous).astype(np.float32)
        delta[~valid[:, :MAX_ACTION_H]] = 0.0
        delta_norm = safe_norm(delta, axis=2)
        spread_norm = safe_norm(rollout - current_z[:, None, :], axis=2)

        past_gap = np.zeros((n, MAX_ACTION_H), dtype=np.float32)
        if pred_np is not None:
            for i, (ep_raw, t_raw) in enumerate(anchors):
                ep = int(ep_raw)
                t = int(t_raw)
                limit = int(min(max(ep_len[ep], 1), emb.shape[1]))
                for j in range(MAX_ACTION_H):
                    src = t - MAX_ACTION_H + j
                    if src >= 0 and src + 1 < limit and src < pred_np.shape[1]:
                        past_gap[i, j] = float(np.linalg.norm(pred_np[ep, src] - emb[ep, src + 1]))
        pieces.extend(
            [
                rollout.reshape(n, -1),
                delta.reshape(n, -1),
                delta_norm,
                spread_norm,
                past_gap,
                rollout_valid,
            ]
        )
        audit_feature_groups.extend(
            [
                "lewm_pred_z_rollout",
                "rollout_delta_z",
                "rollout_delta_norm",
                "rollout_spread_norm",
                "past_one_step_gap_proxy_pred_vs_emb",
            ]
        )

    x = np.concatenate(pieces, axis=1).astype(np.float32)
    x = np.where(np.isfinite(x), x, 0.0).astype(np.float32)
    return {
        "x": x,
        "current_z": current_z.astype(np.float32),
        "anchor_ep_t0": anchors,
        "episode": anchors[:, 0].astype(np.int64),
        "feature_groups": np.asarray(audit_feature_groups, dtype=object),
    }


def build_targets(
    labels: dict[str, np.ndarray],
    split: str,
    h_to_idx: dict[int, int],
    q_idx: int,
) -> dict[str, np.ndarray]:
    idx = [h_to_idx[h] for h in TARGET_HORIZONS]
    y = labels[f"{split}_y"][:, idx, :].astype(np.float32)
    valid = labels[f"{split}_valid"][:, idx].astype(bool)
    mean_err = labels[f"{split}_mean_err_to_h"][:, idx].astype(np.float32)
    err_at_h = labels[f"{split}_err_at_h"].astype(np.float32)
    admission_y = np.max(y[:, :, q_idx], axis=1).astype(np.float32)
    alloc_idx = h_to_idx[ALLOC_H]
    alloc_target = labels[f"{split}_mean_err_to_h"][:, alloc_idx].astype(np.float32)
    alloc_valid = labels[f"{split}_valid"][:, alloc_idx].astype(bool)
    tail_cvar = np.max(labels[f"{split}_err_at_h"][:, :ALLOC_H].astype(np.float32), axis=1)
    selective_target = labels[f"{split}_y"][:, alloc_idx, q_idx].astype(np.float32)
    selective_valid = labels[f"{split}_valid"][:, alloc_idx].astype(bool)
    return {
        "y": y,
        "valid": valid,
        "mean_err": mean_err,
        "err_at_h": err_at_h,
        "admission_y": admission_y,
        "alloc_target": alloc_target,
        "alloc_valid": alloc_valid,
        "tail_cvar": tail_cvar,
        "selective_target": selective_target,
        "selective_valid": selective_valid,
    }


def shuffle_train_targets_within_episode(
    targets: dict[str, np.ndarray],
    episode: np.ndarray,
    *,
    seed: int,
) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    out: dict[str, np.ndarray] = {key: np.array(value, copy=True) for key, value in targets.items()}
    shuffle_keys = {
        "y",
        "admission_y",
        "alloc_target",
        "tail_cvar",
        "selective_target",
    }
    present_keys = [key for key in shuffle_keys if key in out]
    for ep in np.unique(episode):
        idx = np.where(episode == ep)[0]
        if len(idx) <= 1:
            continue
        perm = rng.permutation(idx)
        for key in present_keys:
            out[key][idx] = targets[key][perm]
    return out


def next_latent_targets(latents: dict[str, np.ndarray], anchors: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    emb = latents["emb"].astype(np.float32)
    selected_len = latents.get("selected_ep_len")
    ep_len = selected_len.astype(np.int64) if selected_len is not None else np.full(emb.shape[0], emb.shape[1], dtype=np.int64)
    out = np.zeros((len(anchors), emb.shape[-1]), dtype=np.float32)
    valid = np.zeros(len(anchors), dtype=bool)
    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t = int(t_raw)
        limit = int(min(max(ep_len[ep], 1), emb.shape[1]))
        if t + 1 < limit:
            out[i] = emb[ep, t + 1]
            valid[i] = True
    return out, valid


class G2NIntegrated(nn.Module):
    def __init__(self, in_dim: int, latent_dim: int, n_h: int, n_q: int, width: int, depth: int) -> None:
        super().__init__()
        layers: list[nn.Module] = []
        d = in_dim
        for _ in range(depth):
            layers.extend([nn.Linear(d, width), nn.LayerNorm(width), nn.GELU()])
            d = width
        self.trunk = nn.Sequential(*layers) if layers else nn.Identity()
        trunk_dim = width if layers else in_dim
        self.horizon_head = nn.Linear(trunk_dim, n_h * n_q)
        self.tail_head = nn.Linear(trunk_dim, 1)
        self.admission_head = nn.Linear(trunk_dim, 1)
        self.pred_head = nn.Sequential(
            nn.Linear(trunk_dim, width),
            nn.GELU(),
            nn.Linear(width, latent_dim),
        )
        self.n_h = int(n_h)
        self.n_q = int(n_q)

    def forward(self, x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        z = self.trunk(x)
        horizon = self.horizon_head(z).reshape(-1, self.n_h, self.n_q)
        tail = self.tail_head(z).squeeze(-1)
        admission = self.admission_head(z).squeeze(-1)
        pred_next = self.pred_head(z)
        return horizon, tail, admission, pred_next


def init_model(model: nn.Module) -> None:
    for module in model.modules():
        if isinstance(module, nn.Linear):
            nn.init.kaiming_uniform_(module.weight, a=math.sqrt(5.0))
            if module.bias is not None:
                fan_in, _ = nn.init._calculate_fan_in_and_fan_out(module.weight)
                bound = 1.0 / math.sqrt(fan_in) if fan_in > 0 else 0.0
                nn.init.uniform_(module.bias, -bound, bound)


def pairwise_tail_rank_loss(
    score: torch.Tensor,
    target: torch.Tensor,
    episode: torch.Tensor,
    tail_weight: torch.Tensor,
) -> torch.Tensor | None:
    if int(score.numel()) == 0:
        return score.sum() * 0.0
    same = episode[:, None] == episode[None, :]
    upper = torch.triu(torch.ones_like(same, dtype=torch.bool), diagonal=1)
    diff = target[:, None] - target[None, :]
    sign = torch.sign(diff)
    finite_pair = (
        torch.isfinite(score)[:, None]
        & torch.isfinite(score)[None, :]
        & torch.isfinite(target)[:, None]
        & torch.isfinite(target)[None, :]
        & torch.isfinite(tail_weight)[:, None]
        & torch.isfinite(tail_weight)[None, :]
    )
    pair = same & upper & finite_pair & (sign != 0)
    if not bool(pair.any()):
        return score.sum() * 0.0
    score_diff = score[:, None] - score[None, :]
    weights = 0.5 * (tail_weight[:, None] + tail_weight[None, :])
    denom = weights[pair].sum()
    if not bool(torch.isfinite(denom).item()) or float(denom.detach().cpu()) <= 0.0:
        return score.sum() * 0.0
    per = F.softplus(-(score_diff[pair] * sign[pair]))
    return (per * weights[pair]).sum() / denom


def regression_tail_loss(score: torch.Tensor, target_log: torch.Tensor, tail_weight: torch.Tensor) -> torch.Tensor:
    valid = torch.isfinite(score) & torch.isfinite(target_log) & torch.isfinite(tail_weight) & (tail_weight > 0.0)
    if not bool(valid.any()):
        return score.sum() * 0.0
    score_v = score[valid]
    target_v = target_log[valid]
    weight_v = tail_weight[valid]
    denom = weight_v.sum()
    if not bool(torch.isfinite(denom).item()) or float(denom.detach().cpu()) <= 0.0:
        return score.sum() * 0.0
    centered_score = score_v - torch.mean(score_v)
    centered_target = (target_v - torch.mean(target_v)).detach()
    per = F.smooth_l1_loss(centered_score, centered_target, reduction="none")
    return (per * weight_v).sum() / denom


def tail_weights(cvar_tail: np.ndarray) -> np.ndarray:
    cut = float(np.percentile(cvar_tail.astype(np.float64), TAIL_Q))
    indicator = (cvar_tail >= cut).astype(np.float32)
    return (1.0 + TAIL_CVAR_WEIGHT * indicator).astype(np.float32)


def mahalanobis_stats(x_train: np.ndarray) -> dict[str, np.ndarray | float]:
    x64 = x_train.astype(np.float64)
    mu = np.mean(x64, axis=0)
    var = np.var(x64, axis=0)
    dist = np.mean(((x64 - mu) ** 2) / (var + EPS), axis=1)
    threshold = float(np.percentile(dist, 99.0))
    return {"mean": mu.astype(np.float32), "var": var.astype(np.float32), "threshold": threshold}


def mahalanobis_distance(x: np.ndarray, stats: dict[str, np.ndarray | float]) -> np.ndarray:
    mu = np.asarray(stats["mean"], dtype=np.float32)
    var = np.asarray(stats["var"], dtype=np.float32)
    return np.mean(((x.astype(np.float32) - mu) ** 2) / (var + EPS), axis=1).astype(np.float32)


def train_model(
    args: argparse.Namespace,
    x_train: np.ndarray,
    train_targets: dict[str, np.ndarray],
    next_z: np.ndarray,
    next_valid: np.ndarray,
    episode: np.ndarray,
    ood_distance: np.ndarray,
    ood_threshold: float,
    *,
    device: torch.device,
    seed: int,
    n_q: int,
    latent_dim: int,
) -> tuple[G2NIntegrated | None, dict[str, Any]]:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = G2NIntegrated(
        in_dim=x_train.shape[1],
        latent_dim=latent_dim,
        n_h=len(TARGET_HORIZONS),
        n_q=n_q,
        width=int(args.width),
        depth=int(args.depth),
    ).to(device)
    init_model(model)
    opt = torch.optim.AdamW(model.parameters(), lr=float(args.lr), weight_decay=WEIGHT_DECAY)
    generator = torch.Generator(device="cpu").manual_seed(seed + 4703)

    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_targets["y"].astype(np.float32)).to(device)
    valid_t = torch.from_numpy(train_targets["valid"].astype(bool)).to(device)
    admission_y_t = torch.from_numpy(train_targets["admission_y"].astype(np.float32)).to(device)
    alloc_t = torch.from_numpy(train_targets["alloc_target"].astype(np.float32)).to(device)
    alloc_valid_t = torch.from_numpy(train_targets["alloc_valid"].astype(bool)).to(device)
    target_log_t = torch.from_numpy(np.log(train_targets["alloc_target"].astype(np.float64) + EPS).astype(np.float32)).to(device)
    tw_t = torch.from_numpy(tail_weights(train_targets["tail_cvar"].astype(np.float32))).to(device)
    ep_t = torch.from_numpy(episode.astype(np.int64)).to(device)
    next_z_t = torch.from_numpy(next_z.astype(np.float32)).to(device)
    next_valid_t = torch.from_numpy(next_valid.astype(bool)).to(device)
    ood_t = torch.from_numpy((ood_distance > ood_threshold).astype(np.float32)).to(device)

    history = {"horizon": [], "admission": [], "pred": [], "tail": [], "ood": [], "total": []}
    skipped_nonfinite_batches = 0
    consecutive_nonfinite_epochs = 0
    n = int(len(x_train))
    batch = int(args.batch)
    model.train()
    for _epoch in range(int(args.epochs)):
        order = torch.randperm(n, generator=generator)
        epoch_acc = {key: 0.0 for key in history}
        epoch_batches = 0
        epoch_nonfinite_batches = 0
        epoch_total_batches = 0
        for lo in range(0, n, batch):
            epoch_total_batches += 1
            idx = order[lo : lo + batch].to(device)
            logits, tail_score, admission_score, pred_next = model(x_t[idx])

            per_bce = F.binary_cross_entropy_with_logits(logits, y_t[idx], reduction="none")
            mask = valid_t[idx].float()[:, :, None]
            horizon_loss = (per_bce * mask).sum() / mask.sum().clamp_min(1.0)
            admission_loss = F.binary_cross_entropy_with_logits(admission_score, admission_y_t[idx])

            pred_mask = next_valid_t[idx]
            if bool(pred_mask.any()):
                pred_loss = F.smooth_l1_loss(pred_next[pred_mask], next_z_t[idx][pred_mask])
            else:
                pred_loss = pred_next.sum() * 0.0

            alloc_mask = alloc_valid_t[idx]
            if bool(alloc_mask.any()):
                rank_loss = pairwise_tail_rank_loss(
                    tail_score[alloc_mask],
                    alloc_t[idx][alloc_mask],
                    ep_t[idx][alloc_mask],
                    tw_t[idx][alloc_mask],
                )
                reg_loss = regression_tail_loss(tail_score[alloc_mask], target_log_t[idx][alloc_mask], tw_t[idx][alloc_mask])
                tail_loss = reg_loss if rank_loss is None else rank_loss + TAIL_REG_WEIGHT * reg_loss
            else:
                tail_loss = tail_score.sum() * 0.0

            ood_mask = ood_t[idx] > 0.5
            if bool(ood_mask.any()):
                ood_loss = F.binary_cross_entropy_with_logits(
                    admission_score[ood_mask],
                    torch.ones_like(admission_score[ood_mask]),
                )
            else:
                ood_loss = admission_score.sum() * 0.0

            if int(args.pred_only):
                loss = pred_loss
            else:
                loss = horizon_loss + ADMISSION_WEIGHT * admission_loss
                if int(args.use_pred):
                    loss = loss + PRED_WEIGHT * pred_loss
                if int(args.use_tail):
                    loss = loss + TAIL_WEIGHT * tail_loss
                if int(args.use_ood):
                    loss = loss + OOD_WEIGHT * ood_loss

            if not torch.isfinite(loss):
                skipped_nonfinite_batches += 1
                epoch_nonfinite_batches += 1
                opt.zero_grad(set_to_none=True)
                continue
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=5.0)
            opt.step()

            epoch_acc["horizon"] += safe_tensor_scalar(horizon_loss)
            epoch_acc["admission"] += safe_tensor_scalar(admission_loss)
            epoch_acc["pred"] += safe_tensor_scalar(pred_loss)
            epoch_acc["tail"] += safe_tensor_scalar(tail_loss)
            epoch_acc["ood"] += safe_tensor_scalar(ood_loss)
            epoch_acc["total"] += safe_tensor_scalar(loss)
            epoch_batches += 1
        if epoch_batches == 0:
            consecutive_nonfinite_epochs += 1
        else:
            consecutive_nonfinite_epochs = 0
        if epoch_total_batches > 0 and epoch_nonfinite_batches == epoch_total_batches:
            model.eval()
            if device.type == "cuda":
                torch.cuda.empty_cache()
            return None, {
                "status": "fail-closed",
                "reason": f"all training batches had non-finite loss in epoch {_epoch + 1}",
                "params_count": int(sum(p.numel() for p in model.parameters())),
                "loss_last": {key: float(vals[-1]) if vals else 0.0 for key, vals in history.items()},
                "loss_first": {key: float(vals[0]) if vals else 0.0 for key, vals in history.items()},
                "skipped_nonfinite_batches": int(skipped_nonfinite_batches),
                "nonfinite_epoch": int(_epoch + 1),
            }
        if consecutive_nonfinite_epochs >= MAX_CONSECUTIVE_NONFINITE_EPOCHS:
            model.eval()
            if device.type == "cuda":
                torch.cuda.empty_cache()
            return None, {
                "status": "fail-closed",
                "reason": f"no valid training step for {MAX_CONSECUTIVE_NONFINITE_EPOCHS} consecutive epochs",
                "params_count": int(sum(p.numel() for p in model.parameters())),
                "loss_last": {key: float(vals[-1]) if vals else 0.0 for key, vals in history.items()},
                "loss_first": {key: float(vals[0]) if vals else 0.0 for key, vals in history.items()},
                "skipped_nonfinite_batches": int(skipped_nonfinite_batches),
                "nonfinite_epoch": int(_epoch + 1),
            }
        denom = float(max(1, epoch_batches))
        for key in history:
            history[key].append(epoch_acc[key] / denom)
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model, {
        "status": "ok",
        "params_count": int(sum(p.numel() for p in model.parameters())),
        "loss_last": {key: float(vals[-1]) if vals else 0.0 for key, vals in history.items()},
        "loss_first": {key: float(vals[0]) if vals else 0.0 for key, vals in history.items()},
        "skipped_nonfinite_batches": int(skipped_nonfinite_batches),
    }


def predict_model(model: G2NIntegrated, x: np.ndarray, device: torch.device, batch: int) -> dict[str, np.ndarray]:
    n = int(len(x))
    h_logits = np.zeros((n, len(TARGET_HORIZONS), model.n_q), dtype=np.float32)
    tail = np.zeros(n, dtype=np.float64)
    admission = np.zeros(n, dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, n, batch):
            hi = min(lo + batch, n)
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            logits, r, s, _pred = model(xb)
            h_logits[lo:hi] = logits.detach().cpu().numpy().astype(np.float32)
            tail[lo:hi] = r.detach().cpu().numpy().astype(np.float64)
            admission[lo:hi] = s.detach().cpu().numpy().astype(np.float64)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return {"horizon_logits": h_logits, "tail": tail, "admission": admission}


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


class LogisticBaseline(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.linear = nn.Linear(in_dim, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.linear(x).squeeze(-1)


def train_logistic_baseline(
    x_train: np.ndarray,
    y_train: np.ndarray,
    *,
    seed: int,
    device: torch.device,
    steps: int = 1200,
    lr: float = 5.0e-3,
) -> tuple[LogisticBaseline, np.ndarray, np.ndarray]:
    mean, scale = fit_standardizer(x_train.astype(np.float32))
    x_std = apply_standardizer(x_train.astype(np.float32), mean, scale)
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = LogisticBaseline(x_std.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(x_std.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_train.astype(np.float32)).to(device)
    pos = float(y_train.sum())
    neg = float(len(y_train) - y_train.sum())
    pos_weight = torch.tensor([neg / max(pos, 1.0)], dtype=torch.float32, device=device)
    for _ in range(steps):
        logits = model(x_t)
        loss = F.binary_cross_entropy_with_logits(logits, y_t, pos_weight=pos_weight)
        if not torch.isfinite(loss):
            raise RuntimeError("non-finite post-hoc logistic loss")
        opt.zero_grad(set_to_none=True)
        loss.backward()
        opt.step()
    model.eval()
    return model, mean, scale


def predict_logistic(model: LogisticBaseline, x: np.ndarray, mean: np.ndarray, scale: np.ndarray, device: torch.device) -> np.ndarray:
    x_std = apply_standardizer(x.astype(np.float32), mean, scale)
    out = np.zeros(len(x_std), dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, len(x_std), 1024):
            hi = min(lo + 1024, len(x_std))
            xb = torch.from_numpy(x_std[lo:hi]).to(device)
            out[lo:hi] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


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


def bootstrap_spearman(score: np.ndarray, truth: np.ndarray, episode: np.ndarray, *, seed: int) -> dict[str, float | None]:
    by_ep = split_by_episode_indices(episode)
    vals: list[float] = []
    for idx in by_ep:
        rho = spearman_one(score[idx], truth[idx])
        if np.isfinite(rho):
            vals.append(float(rho))
    if not vals:
        return {"observed": None, "low": None, "high": None}
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


def conformal_threshold(score: np.ndarray, y: np.ndarray, alpha: float) -> float | None:
    finite = np.isfinite(score) & np.isfinite(y)
    score = score[finite].astype(np.float64)
    y = y[finite].astype(np.float64)
    if len(score) == 0:
        return None
    order = np.argsort(score, kind="mergesort")
    s_sorted = score[order]
    y_sorted = y[order]
    cum_fail = np.cumsum(y_sorted)
    n = np.arange(1, len(y_sorted) + 1, dtype=np.float64)
    conservative_risk = (1.0 + cum_fail) / (1.0 + n)
    ok = np.where(conservative_risk <= alpha)[0]
    if len(ok) == 0:
        return None
    return float(s_sorted[int(ok[-1])])


def selective_eval(score: np.ndarray, y: np.ndarray, threshold: float | None) -> dict[str, Any]:
    if threshold is None:
        return {"tau": None, "risk": None, "coverage": 0.0, "risk_le_alpha": False, "admitted": 0, "n": int(len(score))}
    keep = score <= threshold
    coverage = float(np.mean(keep)) if len(score) else 0.0
    risk = float(np.mean(y[keep])) if bool(keep.any()) else None
    return {
        "tau": float(threshold),
        "risk": risk,
        "coverage": coverage,
        "risk_le_alpha": bool(risk is not None and risk <= ALPHA),
        "admitted": int(keep.sum()),
        "n": int(len(score)),
    }


def build_detection(
    train_rows: dict[str, np.ndarray],
    eval_rows: dict[str, np.ndarray],
    labels: dict[str, np.ndarray],
    native_eval_logits: np.ndarray,
    h_to_idx: dict[int, int],
    q_idx: int,
    *,
    device: torch.device,
    seed: int,
) -> dict[str, Any]:
    per_h: dict[str, float] = {}
    paired: dict[str, dict[str, float]] = {}
    for j, h in enumerate(TARGET_HORIZONS):
        source_h_idx = h_to_idx[h]
        train_valid = labels["train_valid"][:, source_h_idx].astype(bool)
        eval_valid = labels["eval_valid"][:, source_h_idx].astype(bool)
        y_train = labels["train_y"][train_valid, source_h_idx, q_idx].astype(np.int8)
        y_eval = labels["eval_y"][eval_valid, source_h_idx, q_idx].astype(np.int8)
        if len(y_train) == 0 or len(y_eval) == 0 or np.unique(y_train).size < 2 or np.unique(y_eval).size < 2:
            per_h[f"h{h}"] = 0.5
            paired[f"h{h}"] = {"observed": 0.0, "low": 0.0, "high": 0.0, "native": 0.5, "posthoc": 0.5}
            continue
        posthoc, mean, scale = train_logistic_baseline(
            train_rows["current_z"][train_valid],
            y_train,
            seed=seed + 1000 + h,
            device=device,
        )
        posthoc_score = predict_logistic(posthoc, eval_rows["current_z"][eval_valid], mean, scale, device)
        native_score = native_eval_logits[eval_valid, j, q_idx].astype(np.float64)
        per_h[f"h{h}"] = float(auroc_rank(y_eval, native_score))
        paired[f"h{h}"] = paired_auroc_delta(
            y_eval,
            native_score,
            posthoc_score,
            eval_rows["episode"][eval_valid],
            seed=seed + BOOTSTRAP_SEED_OFFSET + 100 + h,
        )
    native_h1 = per_h.get("h1")
    strongest_delta = None if native_h1 is None else float(native_h1) - STRONGEST_POSTHOC_H1_AUROC
    return {
        "per_h_auroc": per_h,
        "paired_delta_auroc": paired,
        "strongest_posthoc_h1": float(STRONGEST_POSTHOC_H1_AUROC),
        "strongest_posthoc_h1_source": "Phase1c logistic gap head; scalar benchmark, not paired to this run unless per-anchor scores are provided",
        "native_vs_strongest_posthoc_h1_delta": strongest_delta,
    }


def build_allocation(
    eval_rows: dict[str, np.ndarray],
    labels: dict[str, np.ndarray],
    score: np.ndarray,
    h_to_idx: dict[int, int],
    *,
    seed: int,
) -> dict[str, Any]:
    alloc_idx = h_to_idx[ALLOC_H]
    valid = labels["eval_valid"][:, alloc_idx].astype(bool)
    if int(valid.sum()) == 0:
        return {"delta": None, "ci": {"low": None, "high": None}, "rho": {"observed": None, "low": None, "high": None}}
    anchors = eval_rows["anchor_ep_t0"][valid].astype(np.int64)
    if len(np.unique(anchors[:, 0])) < 2:
        return {"delta": None, "ci": {"low": None, "high": None}, "rho": {"observed": None, "low": None, "high": None}}
    eval_score = score[valid].astype(np.float64)
    errors_h5 = labels["eval_err_at_h"][valid, :ALLOC_H].astype(np.float64)
    true_mean_h5 = labels["eval_mean_err_to_h"][valid, alloc_idx].astype(np.float64)
    by_ep = anchors_by_episode(anchors)
    uniform_alloc = summarize_allocation(allocation_uniform(by_ep), errors_h5, anchors)
    native_alloc = summarize_allocation(allocation_by_score(anchors, by_ep, eval_score), errors_h5, anchors)
    delta = paired_allocation_delta(native_alloc, uniform_alloc, seed=seed + BOOTSTRAP_SEED_OFFSET)
    rho = bootstrap_spearman(eval_score, true_mean_h5, anchors[:, 0].astype(np.int64), seed=seed + BOOTSTRAP_SEED_OFFSET + 1)
    return {
        "delta": float(delta["observed"]),
        "ci": {"low": float(delta["low"]), "high": float(delta["high"])},
        "rho": rho,
    }


def verdict_detection(detection: dict[str, Any]) -> str:
    vals = [float(v) for v in detection["per_h_auroc"].values()]
    deltas = [v for v in detection["paired_delta_auroc"].values()]
    positive_ci = [d for d in deltas if float(d["low"]) > 0.0]
    if positive_ci:
        return f"pass vs in-runner posthoc: {len(positive_ci)}/{len(deltas)} horizons have paired delta CI above 0; mean AUROC={np.mean(vals):.6f}"
    return f"not passed vs in-runner posthoc: no horizon has paired delta CI above 0; mean AUROC={np.mean(vals):.6f}"


def verdict_selective(selective: dict[str, Any]) -> str:
    risk = selective.get("risk")
    coverage = float(selective.get("coverage", 0.0))
    if risk is None:
        return f"not passed: no conformal threshold admitted eval samples; coverage={coverage:.6f}"
    if bool(selective.get("risk_le_alpha", False)):
        return f"pass: eval admitted risk={float(risk):.6f} <= alpha={ALPHA:.2f}, coverage={coverage:.6f}"
    return f"not passed: eval admitted risk={float(risk):.6f} > alpha={ALPHA:.2f}, coverage={coverage:.6f}"


def verdict_allocation(allocation: dict[str, Any]) -> str:
    delta = allocation.get("delta")
    ci = allocation.get("ci", {})
    if delta is None or ci.get("low") is None or ci.get("high") is None:
        return "not passed: allocation metric unavailable"
    low = float(ci["low"])
    high = float(ci["high"])
    observed = float(delta)
    if high < 0.0:
        return f"pass: allocation_delta={observed:.9g}, 95% CI=[{low:.9g},{high:.9g}] below 0"
    if low >= 0.0:
        return f"not passed: allocation_delta={observed:.9g}, 95% CI=[{low:.9g},{high:.9g}] on wrong side"
    return f"not passed: allocation_delta={observed:.9g}, 95% CI=[{low:.9g},{high:.9g}] crosses 0"


def build_claim(detection: dict[str, Any], selective: dict[str, Any], allocation: dict[str, Any]) -> str:
    native_h1 = detection.get("per_h_auroc", {}).get("h1")
    in_runner_h1 = detection.get("paired_delta_auroc", {}).get("h1", {}).get("posthoc")
    in_runner_delta_h1 = detection.get("paired_delta_auroc", {}).get("h1", {}).get("observed")
    strongest_h1 = detection.get("strongest_posthoc_h1")
    strongest_delta = detection.get("native_vs_strongest_posthoc_h1_delta")
    if native_h1 is not None and in_runner_h1 is not None and in_runner_delta_h1 is not None:
        in_runner_sentence = (
            f"Native h1 AUROC={float(native_h1):.6f} vs in-runner posthoc h1={float(in_runner_h1):.6f} "
            f"(paired delta={float(in_runner_delta_h1):+.6f}). "
        )
    else:
        in_runner_sentence = "Native vs in-runner posthoc h1 numeric comparison unavailable. "
    if native_h1 is not None and strongest_h1 is not None and strongest_delta is not None:
        strongest_sentence = (
            f"Native h1 AUROC={float(native_h1):.6f} vs strongest post-hoc h1={float(strongest_h1):.6f} "
            f"(numeric delta={float(strongest_delta):+.6f}); paired CI separation is only for the in-runner baseline, "
            "and the strongest-probe comparison is numeric-only unless paired per-anchor scores are available. "
        )
    else:
        strongest_sentence = (
            "Strongest-probe comparison unavailable for this payload; paired CI separation is only for the in-runner baseline. "
        )
    return (
        "Detection " + verdict_detection(detection) + ". "
        + in_runner_sentence
        + strongest_sentence
        + "Selective " + verdict_selective(selective) + ". "
        + "Allocation " + verdict_allocation(allocation) + ". "
        + "No logit distillation term was used; eval labels/errors were read only for final metrics."
    )


def validate_required(latents: dict[str, np.ndarray], labels: dict[str, np.ndarray]) -> None:
    latent_required = ["emb", "action", "pred"]
    label_required = ["horizons", "quantiles"]
    for split in ("train", "calibration", "eval"):
        label_required.extend(
            [
                f"{split}_anchor_ep_t0",
                f"{split}_valid",
                f"{split}_err_at_h",
                f"{split}_mean_err_to_h",
                f"{split}_pred_z",
                f"{split}_y",
            ]
        )
    missing_latent = [k for k in latent_required if k not in latents]
    missing_label = [k for k in label_required if k not in labels]
    if missing_latent or missing_label:
        raise RuntimeError(f"missing latent fields={missing_latent}; missing label fields={missing_label}")


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    t0 = time.perf_counter()
    device, deterministic = configure_determinism(int(args.seed))
    latents_path = Path(args.latents)
    labels_path = Path(args.labels)
    config = {
        "use_rollout": int(args.use_rollout),
        "use_pred": int(args.use_pred),
        "use_tail": int(args.use_tail),
        "use_ood": int(args.use_ood),
        "pred_only": int(args.pred_only),
        "shuffle_labels": int(args.shuffle_labels),
        "width": int(args.width),
        "depth": int(args.depth),
        "batch": int(args.batch),
        "epochs": int(args.epochs),
        "lr": float(args.lr),
    }
    if not latents_path.exists() or not labels_path.exists():
        return {
            "config": config,
            "detection": {},
            "selective": {},
            "allocation": {},
            "health": {"status": "fail-closed", "reason": f"missing inputs: latents={latents_path}, labels={labels_path}"},
            "deterministic": deterministic,
            "reported_claim": "fail-closed: missing inputs; no metric reported.",
        }

    latents = load_npz(latents_path)
    labels = load_npz(labels_path)
    validate_required(latents, labels)
    h_to_idx = horizon_indices(labels)
    q_idx = q75_index(labels)

    train_rows = build_features(latents, labels, "train", use_rollout=bool(int(args.use_rollout)))
    cal_rows = build_features(latents, labels, "calibration", use_rollout=bool(int(args.use_rollout)))
    eval_rows = build_features(latents, labels, "eval", use_rollout=bool(int(args.use_rollout)))

    feature_mean, feature_scale = fit_standardizer(train_rows["x"])
    x_train = apply_standardizer(train_rows["x"], feature_mean, feature_scale)
    x_cal = apply_standardizer(cal_rows["x"], feature_mean, feature_scale)
    x_eval = apply_standardizer(eval_rows["x"], feature_mean, feature_scale)

    train_targets = build_targets(labels, "train", h_to_idx, q_idx)
    if int(args.shuffle_labels):
        train_targets = shuffle_train_targets_within_episode(
            train_targets,
            train_rows["episode"],
            seed=int(args.seed) + 8081,
        )
    next_z_train, next_valid_train = next_latent_targets(latents, train_rows["anchor_ep_t0"])
    ood_stats = mahalanobis_stats(x_train)
    ood_train_dist = mahalanobis_distance(x_train, ood_stats)

    model, train_health = train_model(
        args,
        x_train,
        train_targets,
        next_z_train,
        next_valid_train,
        train_rows["episode"],
        ood_train_dist,
        float(ood_stats["threshold"]),
        device=device,
        seed=int(args.seed) + 17,
        n_q=int(labels["quantiles"].shape[0]),
        latent_dim=int(latents["emb"].shape[-1]),
    )
    if model is None or str(train_health.get("status", "ok")) != "ok":
        health = {
            "status": "fail-closed",
            "reason": str(train_health.get("reason", "training failed closed before evaluation")),
            "params_count": int(train_health.get("params_count", 0)),
            "loss_first": train_health.get("loss_first", {}),
            "loss_last": train_health.get("loss_last", {}),
            "skipped_nonfinite_batches": int(train_health.get("skipped_nonfinite_batches", 0)),
            "device": device.type,
            "wall_time_sec": float(time.perf_counter() - t0),
            "train_n": int(len(x_train)),
            "calibration_n": int(len(x_cal)),
            "eval_n": int(len(x_eval)),
            "input_dim": int(x_train.shape[1]),
        }
        return {
            "config": config,
            "detection": {},
            "selective": {},
            "allocation": {},
            "health": health,
            "deterministic": deterministic,
            "reported_claim": "fail-closed: training produced no valid metric payload; no metric reported.",
        }

    train_pred = predict_model(model, x_train, device, batch=max(512, int(args.batch)))
    cal_pred = predict_model(model, x_cal, device, batch=max(512, int(args.batch)))
    eval_pred = predict_model(model, x_eval, device, batch=max(512, int(args.batch)))
    del train_pred

    detection = build_detection(
        train_rows,
        eval_rows,
        labels,
        eval_pred["horizon_logits"],
        h_to_idx,
        q_idx,
        device=device,
        seed=int(args.seed),
    )

    alloc_idx = h_to_idx[ALLOC_H]
    cal_sel_valid = labels["calibration_valid"][:, alloc_idx].astype(bool)
    eval_sel_valid = labels["eval_valid"][:, alloc_idx].astype(bool)
    cal_tau = conformal_threshold(
        cal_pred["admission"][cal_sel_valid],
        labels["calibration_y"][cal_sel_valid, alloc_idx, q_idx].astype(np.float32),
        ALPHA,
    )
    selective = selective_eval(
        eval_pred["admission"][eval_sel_valid],
        labels["eval_y"][eval_sel_valid, alloc_idx, q_idx].astype(np.float32),
        cal_tau,
    )
    selective["alpha"] = ALPHA
    selective["target"] = f"h{ALLOC_H}_q{Q75}"
    selective["calibration_n"] = int(cal_sel_valid.sum())

    allocation = build_allocation(
        eval_rows,
        labels,
        eval_pred["tail"],
        h_to_idx,
        seed=int(args.seed),
    )

    eval_ood_dist = mahalanobis_distance(x_eval, ood_stats)
    health = {
        "status": "ok",
        "params_count": int(train_health["params_count"]),
        "loss_first": train_health["loss_first"],
        "loss_last": train_health["loss_last"],
        "skipped_nonfinite_batches": int(train_health.get("skipped_nonfinite_batches", 0)),
        "device": device.type,
        "wall_time_sec": float(time.perf_counter() - t0),
        "train_n": int(len(x_train)),
        "calibration_n": int(len(x_cal)),
        "eval_n": int(len(x_eval)),
        "input_dim": int(x_train.shape[1]),
        "feature_groups": [str(x) for x in train_rows["feature_groups"].tolist()],
        "ood": {
            "train_mahalanobis_p99": float(ood_stats["threshold"]),
            "train_outlier_fraction": float(np.mean(ood_train_dist > float(ood_stats["threshold"]))),
            "eval_outlier_fraction": float(np.mean(eval_ood_dist > float(ood_stats["threshold"]))),
            "loss_enabled": bool(int(args.use_ood)),
        },
        "leakage_attestation": {
            "train_standardizer_fit_on": "train features only",
            "ood_stats_fit_on": "train features only",
            "selective_tau_fit_on": "calibration split only",
            "eval_truth_usage": "eval y/err/mean_err_to_h used only after model training for final metrics",
            "posthoc_baseline": "trained on train current latent only; paired bootstrap grouped by eval episode",
            "distillation": "absent: no post-hoc logit or teacher-logit distillation loss",
            "rollout_gap_proxy": "past one-step pred-vs-emb gaps only; no future eval errors are used as features",
        },
    }
    payload = {
        "config": config,
        "detection": detection,
        "selective": selective,
        "allocation": allocation,
        "health": health,
        "deterministic": deterministic,
        "reported_claim": build_claim(detection, selective, allocation),
    }
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--latents", default=str(DEFAULT_LATENTS))
    parser.add_argument("--labels", default=str(DEFAULT_LABELS))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--width", type=positive_int, default=512)
    parser.add_argument("--depth", type=positive_int, default=3)
    parser.add_argument("--batch", type=positive_int, default=256)
    parser.add_argument("--epochs", type=positive_int, default=160)
    parser.add_argument("--lr", type=finite_float, default=5.0e-4)
    parser.add_argument("--use-rollout", type=zero_one, default=1)
    parser.add_argument("--use-pred", type=zero_one, default=1)
    parser.add_argument("--use-tail", type=zero_one, default=1)
    parser.add_argument("--use-ood", type=zero_one, default=1)
    parser.add_argument("--pred-only", type=zero_one, default=0)
    parser.add_argument("--shuffle-labels", type=zero_one, default=0)
    args = parser.parse_args()

    payload = clean_json(build_payload(args))
    claim = str(payload.get("reported_claim", ""))
    if any(token in claim for token in FORBIDDEN_CLAIM_TOKENS):
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
