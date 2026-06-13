from __future__ import annotations

import json
import math
import os
import random
import time
from copy import deepcopy
from pathlib import Path
from typing import Any

os.environ.setdefault("CUBLAS_WORKSPACE_CONFIG", ":4096:8")

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


ROOT = Path(__file__).resolve().parent
NPZ_PATH = ROOT / "tworooms_latent_large.npz"
LABEL_PATH = ROOT / "reports" / "g2n_labels_clean.npz"
JSON_PATH = ROOT / "reports" / "lewm_d_ledger_shaped_reencoder.json"
MD_PATH = ROOT / "reports" / "lewm_d_ledger_shaped_reencoder.md"

SPLIT_SEED = 1701
PERM_SEED = 90210
BOOTSTRAP_SEED = 314159
RUN_SEEDS = (20260611, 20260612, 20260613)
BOOTSTRAPS = 500

WINDOW = 6
HORIZONS = (1, 3, 5, 10)
QUANTILES = (50, 75, 90)
H_TO_LABEL_IDX = {1: 0, 3: 2, 5: 4, 10: 9}
Q_TO_IDX = {50: 0, 75: 1, 90: 2}

G_DIM = 128
P_D_MODEL = 128
P_HEADS = 4
P_FFN = 256
P_LAYERS = 2

EPOCHS = 150
BATCH = 512
LR = 1e-3
WD = 1e-4
LAMBDA_LEDGER = 0.5
PROBE_EPOCHS = 300


def require_inputs() -> None:
    missing = [str(p) for p in (NPZ_PATH, LABEL_PATH) if not p.exists()]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(missing))


def set_all_seeds(seed: int) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)


def setup_determinism(seed: int) -> dict[str, Any]:
    set_all_seeds(seed)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    note: dict[str, Any] = {"requested": True, "enabled": False, "exception": None}
    try:
        torch.use_deterministic_algorithms(True)
        note["enabled"] = bool(torch.are_deterministic_algorithms_enabled())
    except Exception as exc:  # pragma: no cover - depends on local torch build
        note["exception"] = repr(exc)
    return note


def split_episodes(n_ep: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(SPLIT_SEED)
    perm = rng.permutation(n_ep)
    n_train = int(round(0.6 * n_ep))
    n_cal = int(round(0.2 * n_ep))
    train = np.sort(perm[:n_train])
    cal = np.sort(perm[n_train : n_train + n_cal])
    eval_ep = np.sort(perm[n_train + n_cal :])
    return {"train": train, "calibration": cal, "eval": eval_ep}


def output_col(h: int, q: int) -> int:
    return HORIZONS.index(h) * len(QUANTILES) + Q_TO_IDX[q]


def sigmoid_np(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


def auroc_rank(y_true: np.ndarray, score: np.ndarray) -> float:
    y = y_true.astype(bool)
    n_pos = int(y.sum())
    n_neg = int((~y).sum())
    if n_pos == 0 or n_neg == 0:
        return 0.5
    order = np.argsort(score, kind="mergesort")
    sorted_score = score[order]
    ranks = np.empty(len(score), dtype=np.float64)
    i = 0
    while i < len(score):
        j = i + 1
        while j < len(score) and sorted_score[j] == sorted_score[i]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        ranks[order[i:j]] = avg_rank
        i = j
    return float((ranks[y].sum() - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg))


def average_ranks(x: np.ndarray) -> np.ndarray:
    order = np.argsort(x, kind="mergesort")
    sx = x[order]
    ranks = np.empty(len(x), dtype=np.float64)
    i = 0
    while i < len(x):
        j = i + 1
        while j < len(x) and sx[j] == sx[i]:
            j += 1
        ranks[order[i:j]] = (i + 1 + j) / 2.0
        i = j
    return ranks


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    m = np.isfinite(x) & np.isfinite(y)
    if int(m.sum()) < 3:
        return float("nan")
    rx = average_ranks(x[m].astype(np.float64))
    ry = average_ranks(y[m].astype(np.float64))
    rx -= rx.mean()
    ry -= ry.mean()
    den = float(np.sqrt(np.sum(rx * rx) * np.sum(ry * ry)))
    return float(np.sum(rx * ry) / den) if den > 0 else float("nan")


def metric_auroc(y: np.ndarray, score: np.ndarray) -> dict[str, Any]:
    return {
        "auroc": float(auroc_rank(y.astype(np.int8), score.astype(np.float64))),
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
        "label_rate": float(np.mean(y)) if len(y) else float("nan"),
    }


def paired_bootstrap_delta_auc(
    y: np.ndarray,
    score_left: np.ndarray,
    score_right: np.ndarray,
    cluster: np.ndarray,
    *,
    seed: int = BOOTSTRAP_SEED,
    n_boot: int = BOOTSTRAPS,
) -> dict[str, float]:
    observed = float(auroc_rank(y, score_left) - auroc_rank(y, score_right))
    unique = np.unique(cluster)
    by_cluster = [np.where(cluster == c)[0] for c in unique]
    rng = np.random.default_rng(seed)
    vals = np.zeros(n_boot, dtype=np.float64)
    for b in range(n_boot):
        sampled = rng.integers(0, len(by_cluster), size=len(by_cluster))
        idx = np.concatenate([by_cluster[i] for i in sampled])
        vals[b] = auroc_rank(y[idx], score_left[idx]) - auroc_rank(y[idx], score_right[idx])
    return {
        "observed": observed,
        "bootstrap_mean": float(np.nanmean(vals)),
        "ci95_low": float(np.nanpercentile(vals, 2.5)),
        "ci95_high": float(np.nanpercentile(vals, 97.5)),
        "bootstrap_resamples": int(n_boot),
        "bootstrap_seed": int(seed),
    }


def linear_cka(x: np.ndarray, y: np.ndarray) -> float:
    x = x.astype(np.float64)
    y = y.astype(np.float64)
    x = x - x.mean(axis=0, keepdims=True)
    y = y - y.mean(axis=0, keepdims=True)
    xy = x.T @ y
    xx = x.T @ x
    yy = y.T @ y
    num = float(np.sum(xy * xy))
    den = float(np.sqrt(np.sum(xx * xx) * np.sum(yy * yy)))
    return float(num / den) if den > 0 else float("nan")


def representation_stats(z_orig: np.ndarray, z_prime: np.ndarray) -> dict[str, Any]:
    zp = z_prime.astype(np.float64)
    var = zp.var(axis=0)
    total = float(var.sum())
    if total > 0:
        p = var / total
        p = p[p > 0]
        effective_rank = float(np.exp(-np.sum(p * np.log(p))))
    else:
        effective_rank = 0.0
    norm = np.linalg.norm(zp, axis=1)
    return {
        "pooled_rows": int(zp.shape[0]),
        "dim": int(zp.shape[1]),
        "variance_mean": float(var.mean()),
        "variance_min": float(var.min()),
        "variance_max": float(var.max()),
        "variance_sum": total,
        "effective_rank": effective_rank,
        "small_variance_fraction_lt_1e-6": float(np.mean(var < 1e-6)),
        "norm_mean": float(norm.mean()),
        "norm_std": float(norm.std()),
        "linear_cka_original_meanpool_vs_zprime": linear_cka(z_orig, z_prime),
        "collapse_flag": bool(effective_rank < 5.0 or float(var.mean()) < 1e-6),
    }


def build_examples(data: dict[str, np.ndarray], labels: np.lib.npyio.NpzFile, split: str) -> dict[str, np.ndarray]:
    anchors = labels[f"{split}_anchor_ep_t0"].astype(np.int64)
    emb = data["emb"].astype(np.float32)
    act = data["action"].astype(np.float32)
    target = data["transition_target_emb"].astype(np.float32)
    trans_mask = data["transition_mask"].astype(bool)
    n = len(anchors)
    past_z = np.zeros((n, WINDOW, emb.shape[-1]), dtype=np.float32)
    past_a = np.zeros((n, WINDOW, act.shape[-1]), dtype=np.float32)
    next_z = np.zeros((n, emb.shape[-1]), dtype=np.float32)
    next_valid = np.zeros(n, dtype=bool)
    t_scalar = np.zeros(n, dtype=np.float32)

    y = np.zeros((n, len(HORIZONS), len(QUANTILES)), dtype=np.float32)
    valid = np.zeros_like(y, dtype=bool)
    clean_y = labels[f"{split}_y"].astype(np.int8)
    clean_valid = labels[f"{split}_valid"].astype(bool)
    mean_err_to_h = labels[f"{split}_mean_err_to_h"].astype(np.float64)

    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t0 = int(t_raw)
        vt = int(trans_mask[ep].sum())
        t_scalar[i] = 0.0 if vt <= 1 else float(t0 / max(1, vt - 1))
        for w in range(WINDOW):
            src = max(0, t0 - WINDOW + 1 + w)
            past_z[i, w] = emb[ep, src]
            past_a[i, w] = act[ep, src]
        if t0 < target.shape[1] and trans_mask[ep, t0]:
            next_z[i] = target[ep, t0]
            next_valid[i] = True
        for h_i, h in enumerate(HORIZONS):
            src_h = H_TO_LABEL_IDX[h]
            if clean_valid[i, src_h]:
                y[i, h_i] = clean_y[i, src_h]
                valid[i, h_i] = True

    return {
        "past_z": past_z,
        "past_a": past_a,
        "next_z": next_z,
        "next_valid": next_valid,
        "t_scalar": t_scalar,
        "episode": anchors[:, 0].astype(np.int64),
        "anchor_ep_t0": anchors,
        "y": y,
        "valid": valid,
        "mean_err_to_h": mean_err_to_h,
        "original_meanpool": past_z.mean(axis=1).astype(np.float32),
    }


def compute_norm(train: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    z = train["past_z"].reshape(-1, train["past_z"].shape[-1])
    a = train["past_a"].reshape(-1, train["past_a"].shape[-1])
    target = train["next_z"][train["next_valid"]]
    target_centered = target - target.mean(axis=0, keepdims=True)
    target_scale = float(np.mean(target_centered * target_centered))
    return {
        "z_mean": z.mean(axis=0).astype(np.float32),
        "z_std": (z.std(axis=0) + 1e-6).astype(np.float32),
        "a_mean": a.mean(axis=0).astype(np.float32),
        "a_std": (a.std(axis=0) + 1e-6).astype(np.float32),
        "pred_mse_scale": np.asarray(max(target_scale, 1e-8), dtype=np.float32),
    }


def apply_norm(ex: dict[str, np.ndarray], norm: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    out = dict(ex)
    out["past_z"] = ((ex["past_z"] - norm["z_mean"]) / norm["z_std"]).astype(np.float32)
    out["past_a"] = ((ex["past_a"] - norm["a_mean"]) / norm["a_std"]).astype(np.float32)
    return out


def permute_labels_within_train_episode(ex: dict[str, np.ndarray], seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    y_perm = ex["y"].copy()
    episodes = np.unique(ex["episode"])
    for h_i in range(len(HORIZONS)):
        for q_i in range(len(QUANTILES)):
            for ep in episodes:
                m = (ex["episode"] == ep) & ex["valid"][:, h_i, q_i]
                vals = y_perm[m, h_i, q_i].copy()
                if len(vals) > 1:
                    y_perm[m, h_i, q_i] = vals[rng.permutation(len(vals))]
    return y_perm


class ReEncoder(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.net = nn.Sequential(nn.LayerNorm(192), nn.Linear(192, 256), nn.GELU(), nn.Linear(256, G_DIM))

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class Predictor(nn.Module):
    def __init__(self, act_dim: int) -> None:
        super().__init__()
        self.action_emb = nn.Linear(act_dim, P_D_MODEL)
        self.pos = nn.Parameter(torch.zeros(WINDOW, P_D_MODEL))
        layer = nn.TransformerEncoderLayer(
            d_model=P_D_MODEL,
            nhead=P_HEADS,
            dim_feedforward=P_FFN,
            dropout=0.0,
            batch_first=True,
            norm_first=True,
        )
        self.encoder = nn.TransformerEncoder(layer, num_layers=P_LAYERS)
        self.head = nn.Linear(P_D_MODEL, 192)

    def forward(self, z_prime: torch.Tensor, action: torch.Tensor) -> torch.Tensor:
        x = z_prime + self.action_emb(action) + self.pos.unsqueeze(0)
        h = self.encoder(x)
        return self.head(h[:, -1])


class LedgerHead(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.head = nn.Linear(G_DIM, len(HORIZONS) * len(QUANTILES))

    def forward(self, z_prime: torch.Tensor) -> torch.Tensor:
        return self.head(z_prime.mean(dim=1))


class ArmModel(nn.Module):
    def __init__(self, act_dim: int) -> None:
        super().__init__()
        self.g = ReEncoder()
        self.predictor = Predictor(act_dim)
        self.ledger = LedgerHead()

    def forward(self, z: torch.Tensor, a: torch.Tensor, *, detach_ledger: bool = False) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        z_prime = self.g(z)
        pred = self.predictor(z_prime, a)
        ledger_in = z_prime.detach() if detach_ledger else z_prime
        logits = self.ledger(ledger_in)
        return pred, logits, z_prime


def bce_ledger_loss(logits: torch.Tensor, y: torch.Tensor, valid: torch.Tensor) -> torch.Tensor:
    flat_logits = logits.reshape(-1)
    flat_y = y.reshape(-1)
    flat_valid = valid.reshape(-1)
    if int(flat_valid.sum().item()) == 0:
        return logits.sum() * 0.0
    return F.binary_cross_entropy_with_logits(flat_logits[flat_valid], flat_y[flat_valid])


def batch_tensors(ex: dict[str, np.ndarray], device: torch.device) -> dict[str, torch.Tensor]:
    return {
        "past_z": torch.from_numpy(ex["past_z"]).to(device),
        "past_a": torch.from_numpy(ex["past_a"]).to(device),
        "next_z": torch.from_numpy(ex["next_z"]).to(device),
        "next_valid": torch.from_numpy(ex["next_valid"]).to(device),
        "y": torch.from_numpy(ex["y"].reshape(len(ex["y"]), -1)).to(device),
        "valid": torch.from_numpy(ex["valid"].reshape(len(ex["valid"]), -1)).to(device),
    }


@torch.no_grad()
def evaluate_arm_model(
    model: ArmModel,
    ex: dict[str, np.ndarray],
    device: torch.device,
    pred_mse_scale: float,
) -> dict[str, Any]:
    model.eval()
    logits_chunks: list[np.ndarray] = []
    z_chunks: list[np.ndarray] = []
    mse_chunks: list[np.ndarray] = []
    for lo in range(0, len(ex["past_z"]), BATCH):
        hi = min(len(ex["past_z"]), lo + BATCH)
        z = torch.from_numpy(ex["past_z"][lo:hi]).to(device)
        a = torch.from_numpy(ex["past_a"][lo:hi]).to(device)
        target = torch.from_numpy(ex["next_z"][lo:hi]).to(device)
        pred, logits, z_prime = model(z, a, detach_ledger=False)
        mse = torch.mean((pred - target) ** 2, dim=-1)
        logits_chunks.append(logits.detach().cpu().numpy().astype(np.float64))
        z_chunks.append(z_prime.mean(dim=1).detach().cpu().numpy().astype(np.float32))
        mse_chunks.append(mse.detach().cpu().numpy().astype(np.float64))
    logits_np = np.concatenate(logits_chunks, axis=0)
    z_np = np.concatenate(z_chunks, axis=0)
    mse_np = np.concatenate(mse_chunks, axis=0)
    valid_next = ex["next_valid"].astype(bool)
    return {
        "logits": logits_np,
        "probs": sigmoid_np(logits_np),
        "zprime_meanpool": z_np,
        "one_step_mse_per_row": mse_np,
        "one_step_mse": float(np.mean(mse_np[valid_next])),
        "one_step_mse_norm": float(np.mean(mse_np[valid_next]) / pred_mse_scale),
    }


def calibration_score(model: ArmModel, cal: dict[str, np.ndarray], device: torch.device, pred_mse_scale: float) -> dict[str, float]:
    ev = evaluate_arm_model(model, cal, device, pred_mse_scale)
    logits = torch.from_numpy(ev["logits"]).to(device)
    y = torch.from_numpy(cal["y"].reshape(len(cal["y"]), -1)).to(device)
    valid = torch.from_numpy(cal["valid"].reshape(len(cal["valid"]), -1)).to(device)
    with torch.no_grad():
        ledger_bce = float(bce_ledger_loss(logits, y, valid).detach().cpu().item())
    score = float(ev["one_step_mse_norm"] + LAMBDA_LEDGER * ledger_bce)
    return {
        "cal_score": score,
        "pred_mse_norm": float(ev["one_step_mse_norm"]),
        "ledger_bce": ledger_bce,
    }


def train_arm(
    arm: str,
    seed: int,
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    norm: dict[str, np.ndarray],
    device: torch.device,
) -> tuple[ArmModel, dict[str, Any]]:
    set_all_seeds(seed)
    model = ArmModel(act_dim=train["past_a"].shape[-1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WD)
    tensors = batch_tensors(train, device)
    cal_score_best: dict[str, float] | None = None
    best_state: dict[str, torch.Tensor] | None = None
    pred_mse_scale = float(norm["pred_mse_scale"])
    n = len(train["past_z"])
    y_for_train = train["y"].copy()
    if arm == "C_perm_ledger":
        y_for_train = permute_labels_within_train_episode(train, PERM_SEED)
    y_train_flat = torch.from_numpy(y_for_train.reshape(n, -1)).to(device)

    history: list[dict[str, float]] = []
    for epoch in range(1, EPOCHS + 1):
        model.train()
        perm_gen = torch.Generator(device="cpu")
        perm_gen.manual_seed(seed + epoch * 1009)
        order = torch.randperm(n, generator=perm_gen).numpy()
        total_loss = 0.0
        total_pred = 0.0
        total_led = 0.0
        nb = 0
        for lo in range(0, n, BATCH):
            idx_np = order[lo : lo + BATCH]
            idx = torch.from_numpy(idx_np).to(device)
            pred, logits, _ = model(
                tensors["past_z"][idx],
                tensors["past_a"][idx],
                detach_ledger=(arm == "A_pred_only"),
            )
            next_valid = tensors["next_valid"][idx]
            pred_loss = F.mse_loss(pred[next_valid], tensors["next_z"][idx][next_valid])
            led_loss = bce_ledger_loss(logits, y_train_flat[idx], tensors["valid"][idx])
            if arm == "A_pred_only":
                # Dummy ledger head is trained on detached z' for checkpoint comparability;
                # the re-encoder receives only the prediction loss gradient.
                loss = pred_loss + LAMBDA_LEDGER * led_loss
            elif arm in ("B_ledger_shaped", "C_perm_ledger"):
                loss = pred_loss + LAMBDA_LEDGER * led_loss
            else:
                raise ValueError(arm)
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
            total_loss += float(loss.detach().cpu().item())
            total_pred += float(pred_loss.detach().cpu().item())
            total_led += float(led_loss.detach().cpu().item())
            nb += 1

        cs = calibration_score(model, cal, device, pred_mse_scale)
        if cal_score_best is None or cs["cal_score"] < cal_score_best["cal_score"]:
            cal_score_best = dict(cs)
            cal_score_best["epoch"] = int(epoch)
            best_state = {k: v.detach().cpu().clone() for k, v in model.state_dict().items()}
        if epoch in (1, 25, 50, 75, 100, 125, 150):
            history.append(
                {
                    "epoch": int(epoch),
                    "train_loss": float(total_loss / max(1, nb)),
                    "train_pred_mse": float(total_pred / max(1, nb)),
                    "train_ledger_bce": float(total_led / max(1, nb)),
                    **cs,
                }
            )
            print(
                f"[train] seed={seed} arm={arm} epoch={epoch} "
                f"loss={total_loss/max(1, nb):.6f} cal={cs['cal_score']:.6f}",
                flush=True,
            )

    assert best_state is not None and cal_score_best is not None
    model.load_state_dict(best_state)
    return model, {
        "best_checkpoint": cal_score_best,
        "history": history,
        "ledger_gradient_to_g": bool(arm != "A_pred_only"),
        "label_source": "true_train_labels" if arm != "C_perm_ledger" else f"episode_within_train_permutation_seed_{PERM_SEED}",
    }


class LinearProbe(nn.Module):
    def __init__(self, dim: int) -> None:
        super().__init__()
        self.linear = nn.Linear(dim, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.linear(x).squeeze(-1)


def train_probe(
    train_x: np.ndarray,
    train_y: np.ndarray,
    eval_x: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> tuple[np.ndarray, dict[str, Any]]:
    set_all_seeds(seed)
    model = LinearProbe(train_x.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WD)
    x = torch.from_numpy(train_x.astype(np.float32)).to(device)
    y = torch.from_numpy(train_y.astype(np.float32)).to(device)
    n = len(train_x)
    for epoch in range(1, PROBE_EPOCHS + 1):
        perm_gen = torch.Generator(device="cpu")
        perm_gen.manual_seed(seed + 500_000 + epoch * 917)
        order = torch.randperm(n, generator=perm_gen).numpy()
        model.train()
        for lo in range(0, n, BATCH):
            idx = torch.from_numpy(order[lo : lo + BATCH]).to(device)
            loss = F.binary_cross_entropy_with_logits(model(x[idx]), y[idx])
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    with torch.no_grad():
        ex = torch.from_numpy(eval_x.astype(np.float32)).to(device)
        logits = model(ex).detach().cpu().numpy().astype(np.float64)
        train_logits = model(x).detach().cpu().numpy().astype(np.float64)
        train_loss = float(F.binary_cross_entropy_with_logits(torch.from_numpy(train_logits).to(device), y).detach().cpu().item())
    return sigmoid_np(logits), {"epochs": int(PROBE_EPOCHS), "train_bce": train_loss}


def eval_joint_ledger(probs: np.ndarray, ex: dict[str, np.ndarray], h: int, q: int) -> dict[str, Any]:
    col = output_col(h, q)
    h_i = HORIZONS.index(h)
    q_i = Q_TO_IDX[q]
    m = ex["valid"][:, h_i, q_i].astype(bool)
    y = ex["y"][m, h_i, q_i].astype(np.int8)
    score = probs[m, col]
    return metric_auroc(y, score)


def write_markdown(report: dict[str, Any]) -> None:
    def auc_cell(m: dict[str, Any]) -> str:
        return f"{m['auroc']:.4f}"

    pooled = report["pooled"]
    lines = [
        "# LeWM D: Ledger-Shaped Re-Encoder",
        "",
        f"- verdict: `{report['verdict']['status']}`",
        f"- rule: {report['verdict']['rule']}",
        f"- device: `{report['environment']['device_name']}`; torch `{report['environment']['torch_version']}`; cuda `{report['environment']['torch_cuda_version']}`",
        "",
        "## Frozen Probe AUROC",
        "",
        "| arm | h1 q75 | h5 q75 |",
        "|---|---:|---:|",
    ]
    for arm in ("A_pred_only", "B_ledger_shaped", "C_perm_ledger"):
        lines.append(
            f"| `{arm}` | {auc_cell(pooled['frozen_probe'][arm]['h1_q75'])} | "
            f"{auc_cell(pooled['frozen_probe'][arm]['h5_q75'])} |"
        )
    d_ba = pooled["paired_delta"]["B_minus_A"]
    d_ca = pooled["paired_delta"]["C_minus_A"]
    lines.extend(
        [
            "",
            "## Paired Episode Bootstrap Delta",
            "",
            f"- h1 q75 B-A: observed `{d_ba['h1_q75']['observed']:.4f}`, CI95 "
            f"`[{d_ba['h1_q75']['ci95_low']:.4f}, {d_ba['h1_q75']['ci95_high']:.4f}]`",
            f"- h5 q75 B-A guard: observed `{d_ba['h5_q75']['observed']:.4f}`, CI95 "
            f"`[{d_ba['h5_q75']['ci95_low']:.4f}, {d_ba['h5_q75']['ci95_high']:.4f}]`",
            f"- h1 q75 C-A control: observed `{d_ca['h1_q75']['observed']:.4f}`, CI95 "
            f"`[{d_ca['h1_q75']['ci95_low']:.4f}, {d_ca['h1_q75']['ci95_high']:.4f}]`",
            "",
            "## Guards",
            "",
            f"- h5 B-A CI low > -0.02: `{report['guards']['h5_q75_B_minus_A_ci_low_gt_minus_0p02']['passed']}`",
            f"- B eval one-step latent MSE <= 1.10*A: `{report['guards']['B_eval_mse_not_worse_than_A_by_10pct']['passed']}`",
            f"- C_perm not positive: `{report['guards']['C_perm_not_positive']['passed']}`",
            "",
            "## Not Claimed",
            "",
            report["not_claimed"],
        ]
    )
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    started = time.time()
    require_inputs()
    if not torch.cuda.is_available():
        raise SystemExit("cuda is required for this protocol, but torch.cuda.is_available() is false")
    device = torch.device("cuda")
    det_note = setup_determinism(RUN_SEEDS[0])

    data_npz = np.load(NPZ_PATH, allow_pickle=True)
    labels = np.load(LABEL_PATH, allow_pickle=True)
    data = {k: data_npz[k] for k in data_npz.files}
    expected = split_episodes(int(data["emb"].shape[0]))
    split_check = {
        split: {
            "expected_episodes": int(len(expected[split])),
            "label_episodes": int(len(np.unique(labels[f"{split}_anchor_ep_t0"][:, 0]))),
            "matches_g2n_split": bool(np.array_equal(np.unique(labels[f"{split}_anchor_ep_t0"][:, 0]), expected[split])),
        }
        for split in ("train", "calibration", "eval")
    }
    if not all(v["matches_g2n_split"] for v in split_check.values()):
        raise SystemExit("label anchor episodes do not match split seed 1701")

    raw_train = build_examples(data, labels, "train")
    raw_cal = build_examples(data, labels, "calibration")
    raw_eval = build_examples(data, labels, "eval")
    norm = compute_norm(raw_train)
    train = apply_norm(raw_train, norm)
    cal = apply_norm(raw_cal, norm)
    eval_ex = apply_norm(raw_eval, norm)

    arms = ("A_pred_only", "B_ledger_shaped", "C_perm_ledger")
    report_arms: dict[str, dict[str, Any]] = {arm: {"seeds": {}} for arm in arms}
    pooled_rows: dict[str, dict[str, list[np.ndarray]]] = {
        arm: {
            "h1_score": [],
            "h5_score": [],
            "h1_y": [],
            "h5_y": [],
            "h1_cluster": [],
            "h5_cluster": [],
            "mse": [],
        }
        for arm in arms
    }
    pooled_eval_mse: dict[str, list[float]] = {arm: [] for arm in arms}

    for seed_i, seed in enumerate(RUN_SEEDS):
        print(f"[seed] {seed}", flush=True)
        models: dict[str, ArmModel] = {}
        train_eval_cache: dict[str, dict[str, Any]] = {}
        eval_cache: dict[str, dict[str, Any]] = {}
        for arm in arms:
            model, train_info = train_arm(arm, seed, train, cal, norm, device)
            models[arm] = model
            train_eval_cache[arm] = evaluate_arm_model(model, train, device, float(norm["pred_mse_scale"]))
            eval_cache[arm] = evaluate_arm_model(model, eval_ex, device, float(norm["pred_mse_scale"]))
            pooled_eval_mse[arm].append(float(eval_cache[arm]["one_step_mse"]))

            joint_h1 = eval_joint_ledger(eval_cache[arm]["probs"], eval_ex, 1, 75)
            joint_h5 = eval_joint_ledger(eval_cache[arm]["probs"], eval_ex, 5, 75)
            h1_m = eval_ex["valid"][:, HORIZONS.index(1), Q_TO_IDX[75]].astype(bool)
            h5_m = eval_ex["valid"][:, HORIZONS.index(5), Q_TO_IDX[75]].astype(bool)
            joint_spearman = {
                "h1_q75_score_vs_mean_err_to_h1": spearman(
                    eval_cache[arm]["probs"][h1_m, output_col(1, 75)],
                    eval_ex["mean_err_to_h"][h1_m, H_TO_LABEL_IDX[1]],
                ),
                "h5_q75_score_vs_mean_err_to_h5": spearman(
                    eval_cache[arm]["probs"][h5_m, output_col(5, 75)],
                    eval_ex["mean_err_to_h"][h5_m, H_TO_LABEL_IDX[5]],
                ),
            }
            repr_stats = representation_stats(raw_eval["original_meanpool"], eval_cache[arm]["zprime_meanpool"])

            report_arms[arm]["seeds"][str(seed)] = {
                "training": train_info,
                "joint_ledger_eval": {"h1_q75": joint_h1, "h5_q75": joint_h5, "spearman": joint_spearman},
                "one_step_latent_mse_eval": {
                    "mse": float(eval_cache[arm]["one_step_mse"]),
                    "mse_norm": float(eval_cache[arm]["one_step_mse_norm"]),
                },
                "representation": repr_stats,
            }

        for h in (1, 5):
            h_name = f"h{h}_q75"
            h_i = HORIZONS.index(h)
            q_i = Q_TO_IDX[75]
            train_m = train["valid"][:, h_i, q_i].astype(bool)
            eval_m = eval_ex["valid"][:, h_i, q_i].astype(bool)
            train_y = train["y"][train_m, h_i, q_i].astype(np.int8)
            eval_y = eval_ex["y"][eval_m, h_i, q_i].astype(np.int8)
            clusters = np.asarray([f"{seed}:{int(ep)}" for ep in eval_ex["episode"][eval_m]], dtype=object)
            for arm in arms:
                probe_score, probe_info = train_probe(
                    train_eval_cache[arm]["zprime_meanpool"][train_m],
                    train_y,
                    eval_cache[arm]["zprime_meanpool"][eval_m],
                    seed=seed + 10_000 + h,
                    device=device,
                )
                probe_metric = metric_auroc(eval_y, probe_score)
                report_arms[arm]["seeds"][str(seed)].setdefault("frozen_probe_eval", {})[h_name] = {
                    **probe_metric,
                    "probe_training": probe_info,
                    "input": "mean_pool_frozen_zprime_window_only_no_action",
                }
                pooled_rows[arm][f"h{h}_score"].append(probe_score)
                pooled_rows[arm][f"h{h}_y"].append(eval_y)
                pooled_rows[arm][f"h{h}_cluster"].append(clusters)

    pooled: dict[str, Any] = {"frozen_probe": {}, "paired_delta": {"B_minus_A": {}, "C_minus_A": {}}}
    for arm in arms:
        pooled["frozen_probe"][arm] = {}
        for h in (1, 5):
            y = np.concatenate(pooled_rows[arm][f"h{h}_y"]).astype(np.int8)
            score = np.concatenate(pooled_rows[arm][f"h{h}_score"]).astype(np.float64)
            pooled["frozen_probe"][arm][f"h{h}_q75"] = metric_auroc(y, score)
        pooled["frozen_probe"][arm]["one_step_latent_mse_eval_mean_across_seeds"] = float(np.mean(pooled_eval_mse[arm]))

    for h in (1, 5):
        y_a = np.concatenate(pooled_rows["A_pred_only"][f"h{h}_y"]).astype(np.int8)
        cluster = np.concatenate(pooled_rows["A_pred_only"][f"h{h}_cluster"])
        a_score = np.concatenate(pooled_rows["A_pred_only"][f"h{h}_score"]).astype(np.float64)
        b_score = np.concatenate(pooled_rows["B_ledger_shaped"][f"h{h}_score"]).astype(np.float64)
        c_score = np.concatenate(pooled_rows["C_perm_ledger"][f"h{h}_score"]).astype(np.float64)
        pooled["paired_delta"]["B_minus_A"][f"h{h}_q75"] = paired_bootstrap_delta_auc(y_a, b_score, a_score, cluster)
        pooled["paired_delta"]["C_minus_A"][f"h{h}_q75"] = paired_bootstrap_delta_auc(y_a, c_score, a_score, cluster)

    b_h1 = pooled["paired_delta"]["B_minus_A"]["h1_q75"]
    b_h5 = pooled["paired_delta"]["B_minus_A"]["h5_q75"]
    c_h1 = pooled["paired_delta"]["C_minus_A"]["h1_q75"]
    c_h1_positive = bool(c_h1["ci95_low"] > 0.0 and c_h1["observed"] >= 0.03)
    mse_a = float(pooled["frozen_probe"]["A_pred_only"]["one_step_latent_mse_eval_mean_across_seeds"])
    mse_b = float(pooled["frozen_probe"]["B_ledger_shaped"]["one_step_latent_mse_eval_mean_across_seeds"])
    guards = {
        "primary_h1_B_minus_A_ci_low_gt_0": {"passed": bool(b_h1["ci95_low"] > 0.0), "value": float(b_h1["ci95_low"])},
        "primary_h1_B_minus_A_observed_ge_0p03": {"passed": bool(b_h1["observed"] >= 0.03), "value": float(b_h1["observed"])},
        "C_perm_not_positive": {
            "passed": bool(not c_h1_positive),
            "C_minus_A_h1_positive_definition": "ci95_low > 0 and observed >= 0.03",
            "C_minus_A_h1": c_h1,
        },
        "h5_q75_B_minus_A_ci_low_gt_minus_0p02": {"passed": bool(b_h5["ci95_low"] > -0.02), "value": float(b_h5["ci95_low"])},
        "B_eval_mse_not_worse_than_A_by_10pct": {
            "passed": bool(mse_b <= 1.10 * mse_a),
            "A_eval_mse_mean": mse_a,
            "B_eval_mse_mean": mse_b,
            "ratio_B_over_A": float(mse_b / mse_a),
        },
    }
    d_positive = all(g["passed"] for g in guards.values())
    verdict = {
        "status": "D_positive" if d_positive else "D_negative_bound",
        "rule": (
            "positive iff h1 q75 B-A CI95_low > 0, observed >= 0.03, C_perm not positive, "
            "h5 q75 B-A CI95_low > -0.02, and B one-step latent MSE <= 1.10*A"
        ),
        "interpretation": (
            "ledger gradients entering this re-encoder produced a measurable frozen linear-probe readability gain"
            if d_positive
            else "in this latent export + 8GB budget + re-encoder class, ledger gradients entering the representation did not pass the predeclared measurable linear-readability improvement criteria"
        ),
    }

    environment = {
        "torch_version": torch.__version__,
        "torch_cuda_version": torch.version.cuda,
        "cuda_available": bool(torch.cuda.is_available()),
        "device_name": torch.cuda.get_device_name(0),
        "determinism": det_note,
        "cudnn_benchmark": bool(torch.backends.cudnn.benchmark),
        "cudnn_deterministic": bool(torch.backends.cudnn.deterministic),
    }
    protocol = {
        "seeds": {
            "runs": list(RUN_SEEDS),
            "split": SPLIT_SEED,
            "permutation": PERM_SEED,
            "bootstrap": BOOTSTRAP_SEED,
        },
        "epochs": EPOCHS,
        "batch": BATCH,
        "optimizer": "AdamW",
        "lr": LR,
        "weight_decay": WD,
        "checkpoint_selection": "calibration only, cal_score = pred_mse_norm + 0.5*ledger_bce; no eval early stop or lambda choice",
        "forbidden_inference_probe_inputs": [
            "prediction_mse",
            "err_at_h",
            "mean_err_to_h",
            "observation",
            "pos_*",
            "distance",
            "room labels",
        ],
        "probe_input": "frozen zprime window mean-pool only, no action",
        "A_pred_only_note": "dummy ledger head trained only through detached zprime; ledger BCE cannot update g",
        "pred_mse_norm_scale": "mean squared centered train one-step target latent",
        "split_check": split_check,
    }

    report = {
        "status": "ok",
        "schema_id": "lewm.d.ledger_shaped_reencoder",
        "protocol": protocol,
        "environment": environment,
        "arms": report_arms,
        "pooled": pooled,
        "guards": guards,
        "verdict": verdict,
        "not_claimed": (
            "This is not a theorem about all models or all re-encoders; it only closes boundary D for "
            "tworooms_latent_large.npz + g2n_labels_clean.npz under the declared 8GB-budget architecture, seeds, "
            "split, checkpoint rule, and frozen linear-probe evaluation."
        ),
        "elapsed_sec": float(time.time() - started),
    }
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")
    write_markdown(report)
    print(f"[done] wrote {JSON_PATH} and {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()
