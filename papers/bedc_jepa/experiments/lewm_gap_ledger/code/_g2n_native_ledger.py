from __future__ import annotations

import json
import math
import time
import os
from collections import defaultdict
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn

from _g2n_horizon_labels import load_perturbed_emb
from _lat_lewm_port import NPZ_PATH, REPORT_DIR, split_episodes
from _ledger_gated_rollout import (
    HIGH_H,
    LOW_H,
    MID_H,
    ROLLOUT_BOOTSTRAP_SEED,
    UNIFORM_H,
    allocation_by_score,
    allocation_uniform,
    paired_bootstrap_delta,
    summarize_allocation,
)
from _phase1c_gap_ledger import auroc_rank, flatten_transition_rows, predict_logistic_head
from _phase2a_brittleness_gap import BOOTSTRAPS as PHASE2A_BOOTSTRAPS
from _phase2a_brittleness_gap import clean_json, fit_clean_protocol, perturbation_grid
from _phase2c_ood_aware_gap import (
    cache_path as phase2c_cache_path,
    fit_gap_head_for_parts,
    load_part_cache,
    materialize_clean_split,
)


ROOT = Path(__file__).resolve().parent
CLEAN_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
PERT_LABELS = REPORT_DIR / "g2n_labels_perturbed.npz"
HORIZON_JSON = REPORT_DIR / "g2n_horizon_labels.json"
PHASE2C_JSON = REPORT_DIR / "lewm_ood_aware_gap.json"
LAT_OOD_AWARE_JSON = REPORT_DIR / "lewm_ledger_aware_transformer_ood_aware.json"
JSON_PATH = REPORT_DIR / "g2n_native_ledger.json"
MD_PATH = REPORT_DIR / "g2n_native_ledger.md"
OOD_EMB_CACHE_DIR = REPORT_DIR / "lat_ood_emb_cache"

PYTHON_SEED = 20260611
TORCH_SEED = 20260611
SPLIT_SEED = 1701
MATCHED_RANDOM_SEED = 90210
BOOTSTRAP_SEED = 314159
BOOTSTRAPS = 500

HORIZONS = (1, 3, 5, 10)
QUANTILES = (50, 75, 90)
H_TO_LABEL_IDX = {1: 0, 3: 2, 5: 4, 10: 9}
PERT_H_TO_LABEL_IDX = {1: 0, 3: 2, 5: 4}
Q_TO_IDX = {50: 0, 75: 1, 90: 2}
PRIMARY_H = 1
PRIMARY_Q = 75
BUDGET_H = 5
BUDGET_Q = 75
WINDOW = 6
MAX_FUTURE_TOKENS = 5

D_MODEL = 64
N_HEADS = 4
N_LAYERS = 2
FFN_DIM = 128
EPOCHS = 30
BATCH = 256
LR = 1e-3

LAMBDA_FAIL = 1.0
LAMBDA_TEACHER = 0.5
LAMBDA_UNLOGGED = 0.5
LAMBDA_BUDGET = 0.5

OUTCOME1_C_OBS = 0.721
OUTCOME1_C_CI = (0.678, 0.759)
OUTCOME1_B_OBS = 0.602


def require_inputs() -> None:
    missing = [p for p in (CLEAN_LABELS, PERT_LABELS, HORIZON_JSON) if not p.exists()]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


def pair_to_row_index(rows: dict[str, np.ndarray]) -> dict[tuple[int, int], int]:
    return {(int(ep), int(t)): i for i, (ep, t) in enumerate(zip(rows["episode"], rows["t"]))}


def row_index_to_pair(rows: dict[str, np.ndarray]) -> dict[int, tuple[int, int]]:
    return {i: (int(ep), int(t)) for i, (ep, t) in enumerate(zip(rows["episode"], rows["t"]))}


def valid_transition_count(data: dict[str, np.ndarray], ep: int) -> int:
    return int(data["transition_mask"][ep].astype(bool).sum())


def tensor_metric_observed(y: np.ndarray, prob: np.ndarray) -> dict[str, float]:
    return {
        "failure_detection_auroc": float(auroc_rank(y.astype(np.int8), prob.astype(np.float64))),
        "unlogged_error_rate": float(np.mean((y > 0) & (prob < 0.5))) if len(y) else float("nan"),
        "declared_gap_rate": float(np.mean(prob >= 0.5)) if len(y) else float("nan"),
        "failure_rate": float(np.mean(y)) if len(y) else float("nan"),
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
    }


def bootstrap_failure_metrics(
    y: np.ndarray,
    prob: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int = BOOTSTRAP_SEED,
    n_boot: int = BOOTSTRAPS,
) -> dict[str, dict[str, float]]:
    observed = tensor_metric_observed(y, prob)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    values: dict[str, list[float]] = {k: [] for k in observed}
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        m = tensor_metric_observed(y[idx], prob[idx])
        for k, v in m.items():
            values[k].append(v)
    out: dict[str, dict[str, float]] = {}
    for k, obs in observed.items():
        arr = np.asarray(values[k], dtype=np.float64)
        out[k] = {
            "observed": float(obs),
            "bootstrap_mean": float(np.nanmean(arr)),
            "ci95_low": float(np.nanpercentile(arr, 2.5)),
            "ci95_high": float(np.nanpercentile(arr, 97.5)),
        }
    return out


def output_col(h: int, q: int) -> int:
    return HORIZONS.index(h) * len(QUANTILES) + Q_TO_IDX[q]


def sigmoid_np(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


class NativeLedgerTransformer(nn.Module):
    def __init__(self, emb_dim: int, act_dim: int, *, include_future: bool, action_only: bool) -> None:
        super().__init__()
        self.emb_dim = emb_dim
        self.act_dim = act_dim
        self.include_future = include_future
        self.action_only = action_only
        token_dim = emb_dim * 2 + act_dim + 1
        self.token_proj = nn.Linear(token_dim, D_MODEL)
        self.pos = nn.Parameter(torch.zeros(WINDOW + MAX_FUTURE_TOKENS + 1, D_MODEL))
        self.type_emb = nn.Embedding(3, D_MODEL)
        layer = nn.TransformerEncoderLayer(
            d_model=D_MODEL,
            nhead=N_HEADS,
            dim_feedforward=FFN_DIM,
            dropout=0.0,
            batch_first=True,
            norm_first=True,
        )
        self.encoder = nn.TransformerEncoder(layer, num_layers=N_LAYERS)
        self.head = nn.Linear(D_MODEL, len(HORIZONS) * len(QUANTILES))

    def forward(
        self,
        past_z: torch.Tensor,
        past_a: torch.Tensor,
        future_z: torch.Tensor,
        future_delta: torch.Tensor,
        future_avail: torch.Tensor,
        t_scalar: torch.Tensor,
    ) -> torch.Tensor:
        b = past_z.shape[0]
        if self.action_only:
            past_z = torch.zeros_like(past_z)
            future_z = torch.zeros_like(future_z)
            future_delta = torch.zeros_like(future_delta)
            future_avail = torch.zeros_like(future_avail, dtype=torch.bool)

        t_past = t_scalar[:, None, None].expand(b, WINDOW, 1)
        past = torch.cat(
            [
                past_z,
                torch.zeros(b, WINDOW, self.emb_dim, device=past_z.device, dtype=past_z.dtype),
                past_a,
                t_past,
            ],
            dim=-1,
        )
        pieces = [past]
        type_ids = [torch.zeros(b, WINDOW, device=past_z.device, dtype=torch.long)]
        key_padding = [torch.zeros(b, WINDOW, device=past_z.device, dtype=torch.bool)]

        if self.include_future:
            t_future = t_scalar[:, None, None].expand(b, MAX_FUTURE_TOKENS, 1)
            fut = torch.cat(
                [
                    future_z,
                    future_delta,
                    torch.zeros(b, MAX_FUTURE_TOKENS, self.act_dim, device=past_z.device, dtype=past_z.dtype),
                    t_future,
                ],
                dim=-1,
            )
            pieces.append(fut)
            type_ids.append(torch.ones(b, MAX_FUTURE_TOKENS, device=past_z.device, dtype=torch.long))
            key_padding.append(~future_avail.bool())

        query = torch.zeros(b, 1, self.emb_dim * 2 + self.act_dim + 1, device=past_z.device, dtype=past_z.dtype)
        pieces.append(query)
        type_ids.append(torch.full((b, 1), 2, device=past_z.device, dtype=torch.long))
        key_padding.append(torch.zeros(b, 1, device=past_z.device, dtype=torch.bool))

        x = torch.cat(pieces, dim=1)
        tid = torch.cat(type_ids, dim=1)
        pad = torch.cat(key_padding, dim=1)
        h = self.token_proj(x) + self.type_emb(tid) + self.pos[: x.shape[1]].unsqueeze(0)
        h = self.encoder(h, src_key_padding_mask=pad)
        return self.head(h[:, -1])


def build_clean_examples(
    data: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
    split: str,
    teacher_by_pair: dict[tuple[int, int], float] | None,
) -> dict[str, np.ndarray]:
    anchors = clean[f"{split}_anchor_ep_t0"].astype(np.int64)
    emb_np = data["emb"].astype(np.float32)
    act_np = data["action"].astype(np.float32)
    emb_dim = emb_np.shape[-1]
    act_dim = act_np.shape[-1]
    n = len(anchors)
    past_z = np.zeros((n, WINDOW, emb_dim), dtype=np.float32)
    past_a = np.zeros((n, WINDOW, act_dim), dtype=np.float32)
    future_z = np.zeros((n, MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
    future_delta = np.zeros((n, MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
    future_avail = clean[f"{split}_valid"][:, :MAX_FUTURE_TOKENS].astype(bool)
    pred_z = clean[f"{split}_pred_z"][:, :MAX_FUTURE_TOKENS].astype(np.float32)
    t_scalar = np.zeros(n, dtype=np.float32)
    episode = anchors[:, 0].astype(np.int64)
    y = np.zeros((n, len(HORIZONS), len(QUANTILES)), dtype=np.float32)
    valid = np.zeros_like(y, dtype=bool)
    clean_y = clean[f"{split}_y"].astype(np.int8)
    clean_valid = clean[f"{split}_valid"].astype(bool)
    mean_err_to_h = clean[f"{split}_mean_err_to_h"].astype(np.float64)
    budget_err = np.full(n, np.nan, dtype=np.float64)
    budget_valid = clean_valid[:, H_TO_LABEL_IDX[BUDGET_H]].astype(bool)
    budget_err[budget_valid] = mean_err_to_h[budget_valid, H_TO_LABEL_IDX[BUDGET_H]]
    teacher = np.full(n, np.nan, dtype=np.float32)

    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t0 = int(t_raw)
        vt = valid_transition_count(data, ep)
        t_scalar[i] = 0.0 if vt <= 1 else float(t0 / max(1, vt - 1))
        for w in range(WINDOW):
            src = max(0, t0 - WINDOW + 1 + w)
            past_z[i, w] = emb_np[ep, src]
            past_a[i, w] = act_np[ep, src]
        previous = emb_np[ep, t0]
        for k in range(MAX_FUTURE_TOKENS):
            if future_avail[i, k] and np.isfinite(pred_z[i, k]).all():
                future_z[i, k] = pred_z[i, k]
                future_delta[i, k] = pred_z[i, k] - previous
                previous = pred_z[i, k]
            else:
                future_avail[i, k] = False
        for h_i, h in enumerate(HORIZONS):
            src_h = H_TO_LABEL_IDX[h]
            if clean_valid[i, src_h]:
                y[i, h_i] = clean_y[i, src_h]
                valid[i, h_i] = True
        if teacher_by_pair is not None:
            teacher[i] = float(teacher_by_pair[(ep, t0)])

    return {
        "kind": np.full(n, 0, dtype=np.int8),
        "past_z": past_z,
        "past_a": past_a,
        "future_z": future_z,
        "future_delta": future_delta,
        "future_avail": future_avail,
        "t_scalar": t_scalar,
        "episode": episode,
        "anchor_ep_t0": anchors,
        "y": y,
        "valid": valid,
        "teacher": teacher,
        "teacher_valid": np.isfinite(teacher),
        "budget_err": budget_err,
        "budget_valid": budget_valid,
    }


def build_perturbed_examples(
    data: dict[str, np.ndarray],
    clean_tau_h1: np.ndarray,
    pair_for_row: dict[int, tuple[int, int]],
    parts_by_key: dict[str, dict[str, Any]],
    teacher_by_key_row: dict[tuple[str, int], float],
    *,
    split: str,
    keys: list[str],
    labels: np.lib.npyio.NpzFile | None = None,
) -> dict[str, np.ndarray]:
    emb_dim = data["emb"].shape[-1]
    act_dim = data["action"].shape[-1]
    act_np = data["action"].astype(np.float32)

    chunks: list[dict[str, np.ndarray]] = []
    for key in keys:
        emb_by_ep = load_perturbed_emb(OOD_EMB_CACHE_DIR / f"{split}_{key}.npz")
        if labels is None:
            part = parts_by_key[key]
            row_idx = part["row_idx"].astype(np.int64)
            mse = part["mse"].astype(np.float64)
            pairs = np.asarray([pair_for_row[int(r)] for r in row_idx], dtype=np.int64)
            keep = pairs[:, 1] >= 2
            row_idx = row_idx[keep]
            mse = mse[keep]
            anchors = pairs[keep]
            y_h1 = (mse[:, None] > clean_tau_h1.reshape(1, -1)).astype(np.float32)
            h_valid = np.ones(len(anchors), dtype=bool)
            teacher = np.asarray([teacher_by_key_row[(key, int(r))] for r in row_idx], dtype=np.float32)
        else:
            anchors = labels[f"{key}_anchor_ep_t0"].astype(np.int64)
            y_h1 = labels[f"{key}_y"][:, 0, :].astype(np.float32)
            h_valid = labels[f"{key}_valid"][:, 0].astype(bool)
            row_idx = np.full(len(anchors), -1, dtype=np.int64)
            teacher = np.full(len(anchors), np.nan, dtype=np.float32)

        n = len(anchors)
        past_z = np.zeros((n, WINDOW, emb_dim), dtype=np.float32)
        past_a = np.zeros((n, WINDOW, act_dim), dtype=np.float32)
        future_z = np.zeros((n, MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
        future_delta = np.zeros((n, MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
        future_avail = np.zeros((n, MAX_FUTURE_TOKENS), dtype=bool)
        t_scalar = np.zeros(n, dtype=np.float32)
        y = np.zeros((n, len(HORIZONS), len(QUANTILES)), dtype=np.float32)
        valid = np.zeros_like(y, dtype=bool)
        for i, (ep_raw, t_raw) in enumerate(anchors):
            ep = int(ep_raw)
            t0 = int(t_raw)
            vt = valid_transition_count(data, ep)
            t_scalar[i] = 0.0 if vt <= 1 else float(t0 / max(1, vt - 1))
            seq = emb_by_ep[ep]
            for w in range(WINDOW):
                src = max(0, t0 - WINDOW + 1 + w)
                past_z[i, w] = seq[src]
                past_a[i, w] = act_np[ep, src]
            if h_valid[i]:
                y[i, 0] = y_h1[i]
                valid[i, 0] = True
        chunks.append(
            {
                "kind": np.full(n, 1, dtype=np.int8),
                "row_idx": row_idx,
                "past_z": past_z,
                "past_a": past_a,
                "future_z": future_z,
                "future_delta": future_delta,
                "future_avail": future_avail,
                "t_scalar": t_scalar,
                "episode": anchors[:, 0].astype(np.int64),
                "anchor_ep_t0": anchors,
                "y": y,
                "valid": valid,
                "teacher": teacher,
                "teacher_valid": np.isfinite(teacher),
                "budget_err": np.full(n, np.nan, dtype=np.float64),
                "budget_valid": np.zeros(n, dtype=bool),
                "slice_key": np.asarray([key] * n),
            }
        )
    return concat_examples(chunks)


def concat_examples(parts: list[dict[str, np.ndarray]]) -> dict[str, np.ndarray]:
    if not parts:
        raise ValueError("cannot concatenate empty examples")
    keys = parts[0].keys()
    return {k: np.concatenate([p[k] for p in parts if k in p], axis=0) for k in keys if all(k in p for p in parts)}


def select_outputs_for_arm(ex: dict[str, np.ndarray], arm: str) -> dict[str, np.ndarray]:
    out = {k: (v.copy() if isinstance(v, np.ndarray) else v) for k, v in ex.items()}
    valid = out["valid"].copy()
    if arm == "D":
        valid[:, 1:, :] = False
    out["valid"] = valid
    return out


def compute_norm(ex: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    z = ex["past_z"].reshape(-1, ex["past_z"].shape[-1])
    mean = z.mean(axis=0).astype(np.float32)
    std = (z.std(axis=0) + 1e-6).astype(np.float32)
    fut = ex["future_delta"][ex["future_avail"].astype(bool)]
    if len(fut):
        d_mean = fut.mean(axis=0).astype(np.float32)
        d_std = (fut.std(axis=0) + 1e-6).astype(np.float32)
    else:
        d_mean = np.zeros_like(mean)
        d_std = np.ones_like(std)
    return {"z_mean": mean, "z_std": std, "delta_mean": d_mean, "delta_std": d_std}


def normalize_examples(ex: dict[str, np.ndarray], norm: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    out = {k: v for k, v in ex.items()}
    out = dict(out)
    out["past_z"] = ((ex["past_z"] - norm["z_mean"]) / norm["z_std"]).astype(np.float32)
    out["future_z"] = ((ex["future_z"] - norm["z_mean"]) / norm["z_std"]).astype(np.float32)
    out["future_delta"] = ((ex["future_delta"] - norm["delta_mean"]) / norm["delta_std"]).astype(np.float32)
    return out


def permute_training_labels(ex: dict[str, np.ndarray], seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    out = {k: (v.copy() if isinstance(v, np.ndarray) else v) for k, v in ex.items()}
    for h_i in range(len(HORIZONS)):
        for q_i in range(len(QUANTILES)):
            m = out["valid"][:, h_i, q_i]
            vals = out["y"][m, h_i, q_i].copy()
            out["y"][m, h_i, q_i] = vals[rng.permutation(len(vals))]
    tv = out["teacher_valid"]
    vals_t = out["teacher"][tv].copy()
    out["teacher"][tv] = vals_t[rng.permutation(len(vals_t))]
    bv = out["budget_valid"]
    vals_b = out["budget_err"][bv].copy()
    out["budget_err"][bv] = vals_b[rng.permutation(len(vals_b))]
    return out


def train_arm(
    name: str,
    train_ex: dict[str, np.ndarray],
    *,
    include_future: bool,
    action_only: bool,
    use_teacher: bool,
    use_unlogged: bool,
    use_budget: bool,
    label_permutation_seed: int | None,
) -> tuple[NativeLedgerTransformer, dict[str, Any], dict[str, np.ndarray]]:
    torch.manual_seed(TORCH_SEED)
    np.random.seed(PYTHON_SEED)
    ex = select_outputs_for_arm(train_ex, name)
    if label_permutation_seed is not None:
        ex = permute_training_labels(ex, label_permutation_seed)
    norm = compute_norm(ex)
    exn = normalize_examples(ex, norm)
    model = NativeLedgerTransformer(
        exn["past_z"].shape[-1],
        exn["past_a"].shape[-1],
        include_future=include_future,
        action_only=action_only,
    )
    opt = torch.optim.AdamW(model.parameters(), lr=LR)
    tensors = {
        "past_z": torch.from_numpy(exn["past_z"].astype(np.float32)),
        "past_a": torch.from_numpy(exn["past_a"].astype(np.float32)),
        "future_z": torch.from_numpy(exn["future_z"].astype(np.float32)),
        "future_delta": torch.from_numpy(exn["future_delta"].astype(np.float32)),
        "future_avail": torch.from_numpy(exn["future_avail"].astype(bool)),
        "t_scalar": torch.from_numpy(exn["t_scalar"].astype(np.float32)),
        "y": torch.from_numpy(exn["y"].reshape(len(exn["y"]), -1).astype(np.float32)),
        "valid": torch.from_numpy(exn["valid"].reshape(len(exn["valid"]), -1).astype(bool)),
        "teacher": torch.from_numpy(exn["teacher"].astype(np.float32)),
        "teacher_valid": torch.from_numpy(exn["teacher_valid"].astype(bool)),
        "budget_err": torch.from_numpy(exn["budget_err"].astype(np.float32)),
        "budget_valid": torch.from_numpy(exn["budget_valid"].astype(bool)),
        "episode": torch.from_numpy(exn["episode"].astype(np.int64)),
    }
    generator = torch.Generator().manual_seed(TORCH_SEED)
    n = len(exn["episode"])
    steps = 0
    t0 = time.perf_counter()
    model.train()
    for _ in range(EPOCHS):
        epoch = _ + 1
        order = torch.randperm(n, generator=generator)
        for start in range(0, n, BATCH):
            idx = order[start : start + BATCH]
            logits = model(
                tensors["past_z"][idx],
                tensors["past_a"][idx],
                tensors["future_z"][idx],
                tensors["future_delta"][idx],
                tensors["future_avail"][idx],
                tensors["t_scalar"][idx],
            )
            valid = tensors["valid"][idx]
            y = tensors["y"][idx]
            bce = nn.functional.binary_cross_entropy_with_logits(logits, y, reduction="none")
            n_valid = torch.clamp(valid.sum().float(), min=1.0)
            loss = LAMBDA_FAIL * (bce[valid].sum() / n_valid)

            if use_teacher:
                tv = tensors["teacher_valid"][idx]
                if bool(tv.any()):
                    pred = torch.sigmoid(logits[:, output_col(1, 75)])
                    loss = loss + LAMBDA_TEACHER * nn.functional.mse_loss(pred[tv], tensors["teacher"][idx][tv])

            if use_unlogged:
                fn = valid & (y > 0.5) & (torch.sigmoid(logits) < 0.5)
                loss = loss + LAMBDA_UNLOGGED * (bce[fn].sum() / n_valid)

            if use_budget:
                bv = tensors["budget_valid"][idx]
                if bool(bv.sum() >= 2):
                    local = torch.where(bv)[0]
                    ep = tensors["episode"][idx][local]
                    target = tensors["budget_err"][idx][local]
                    score = logits[local, output_col(5, 75)]
                    same = ep[:, None] == ep[None, :]
                    upper = torch.triu(torch.ones_like(same, dtype=torch.bool), diagonal=1)
                    target_diff = target[:, None] - target[None, :]
                    sign = torch.sign(target_diff)
                    pair = same & upper & (sign != 0)
                    if bool(pair.any()):
                        score_diff = score[:, None] - score[None, :]
                        budget_loss = nn.functional.softplus(-(score_diff[pair] * sign[pair])).mean()
                        loss = loss + LAMBDA_BUDGET * budget_loss

            if not torch.isfinite(loss):
                raise RuntimeError(f"non-finite loss in arm {name}")
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
        if epoch == 1 or epoch % 5 == 0 or epoch == EPOCHS:
            print(f"[train] arm={name} epoch={epoch}/{EPOCHS} steps={steps}", flush=True)
    info = {
        "status": "trained",
        "epochs": EPOCHS,
        "batch": BATCH,
        "optimizer": "AdamW",
        "lr": LR,
        "optimizer_steps": int(steps),
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(n),
        "include_future": bool(include_future),
        "action_only": bool(action_only),
        "use_teacher": bool(use_teacher),
        "use_unlogged": bool(use_unlogged),
        "use_budget": bool(use_budget),
        "label_permutation_seed": label_permutation_seed,
    }
    return model.eval(), info, norm


def predict_logits(
    model: NativeLedgerTransformer,
    ex: dict[str, np.ndarray],
    norm: dict[str, np.ndarray],
    *,
    batch: int = 1024,
) -> np.ndarray:
    exn = normalize_examples(ex, norm)
    out = np.zeros((len(exn["episode"]), len(HORIZONS) * len(QUANTILES)), dtype=np.float64)
    with torch.no_grad():
        for lo in range(0, len(out), batch):
            hi = min(lo + batch, len(out))
            logits = model(
                torch.from_numpy(exn["past_z"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["past_a"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_z"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_delta"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_avail"][lo:hi].astype(bool)),
                torch.from_numpy(exn["t_scalar"][lo:hi].astype(np.float32)),
            )
            out[lo:hi] = logits.detach().cpu().numpy().astype(np.float64)
    return out


def evaluate_clean(logits: np.ndarray, ex: dict[str, np.ndarray]) -> dict[str, Any]:
    probs = sigmoid_np(logits)
    by_h: dict[str, Any] = {}
    for h_i, h in enumerate(HORIZONS):
        q_i = Q_TO_IDX[75]
        m = ex["valid"][:, h_i, q_i]
        by_h[f"h{h}_q75"] = bootstrap_failure_metrics(
            ex["y"][m, h_i, q_i].astype(np.int8),
            probs[m, output_col(h, 75)],
            ex["episode"][m],
        )
    return by_h


def evaluate_ood(
    model: NativeLedgerTransformer,
    norm: dict[str, np.ndarray],
    data: dict[str, np.ndarray],
    pert_labels: np.lib.npyio.NpzFile,
    keys: list[str],
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    empty_parts: dict[str, dict[str, Any]] = {}
    for key in keys:
        ex = build_perturbed_examples(
            data,
            np.zeros(3, dtype=np.float64),
            {},
            empty_parts,
            {},
            split="eval",
            keys=[key],
            labels=pert_labels,
        )
        logits = predict_logits(model, ex, norm)
        probs = sigmoid_np(logits)
        by_h: dict[str, Any] = {}
        for h in (1, 3, 5):
            h_i = HORIZONS.index(h)
            src_i = PERT_H_TO_LABEL_IDX[h]
            q_i = Q_TO_IDX[75]
            m = pert_labels[f"{key}_valid"][:, src_i].astype(bool)
            y = pert_labels[f"{key}_y"][:, src_i, q_i].astype(np.int8)
            by_h[f"h{h}_q75"] = bootstrap_failure_metrics(y[m], probs[m, output_col(h, 75)], ex["episode"][m])
            by_h[f"h{h}_q75"]["single_class_truth"] = bool(np.unique(y[m]).size < 2)
        out[key] = by_h
    return out


def load_phase2c_perturb_train_parts(report: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], list[str]]:
    grids = perturbation_grid()
    families = list(report.get("families_evaluated", grids.keys()))
    parts: dict[str, dict[str, Any]] = {}
    keys: list[str] = []
    for family in families:
        for strength in grids[family]:
            if float(strength) == 0.0:
                continue
            path = phase2c_cache_path(family, float(strength), "train")
            part = load_part_cache(path, family, float(strength), "train", "phase2c_materialized_cache")
            if part is None:
                raise SystemExit(f"missing required phase2c perturb train cache: {path}")
            token = f"{float(strength):g}".replace(".", "p").replace("-", "m")
            key = f"{family}_{token}"
            parts[key] = part
            keys.append(key)
            emb_path = OOD_EMB_CACHE_DIR / f"train_{key}.npz"
            if not emb_path.exists():
                raise SystemExit(f"missing required perturbed embedding cache: {emb_path}")
    return parts, keys


def rebuild_teachers(
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    parts_by_key: dict[str, dict[str, Any]],
    keys: list[str],
) -> dict[str, Any]:
    protocol = fit_clean_protocol(data, rows)
    train_clean = materialize_clean_split(protocol, rows, "train")
    eval_clean = materialize_clean_split(protocol, rows, "eval")
    clean_head, clean_fit = fit_gap_head_for_parts([train_clean])
    ood_head, ood_fit = fit_gap_head_for_parts([train_clean] + [parts_by_key[k] for k in keys])

    phase2c = json.loads(PHASE2C_JSON.read_text(encoding="utf-8"))
    checks = {}
    for name, head in (("clean_only", clean_head), ("ood_aware", ood_head)):
        p, _ = predict_logistic_head(head, eval_clean["x"])
        obs = float(auroc_rank(eval_clean["y"], p))
        target = float(phase2c["arms"][name]["clean_eval"]["observed"]["failure_detection_auroc"])
        delta = abs(obs - target)
        checks[name] = {"observed": obs, "target": target, "abs_delta": delta, "tolerance": 1e-9}
        if delta > 1e-9:
            raise SystemExit(f"teacher anchor failed for {name}: observed={obs:.17g}, target={target:.17g}")

    teacher_clean_by_pair: dict[tuple[int, int], float] = {}
    p1, _ = predict_logistic_head(clean_head, train_clean["x"])
    p2, _ = predict_logistic_head(ood_head, train_clean["x"])
    for row_idx, s1, s2 in zip(train_clean["row_idx"], p1, p2):
        ep, t = int(rows["episode"][int(row_idx)]), int(rows["t"][int(row_idx)])
        teacher_clean_by_pair[(ep, t)] = float((s1 + s2) / 2.0)

    teacher_pert_by_key_row: dict[tuple[str, int], float] = {}
    for key in keys:
        part = parts_by_key[key]
        pp1, _ = predict_logistic_head(clean_head, part["x"])
        pp2, _ = predict_logistic_head(ood_head, part["x"])
        for row_idx, s1, s2 in zip(part["row_idx"], pp1, pp2):
            teacher_pert_by_key_row[(key, int(row_idx))] = float((s1 + s2) / 2.0)

    return {
        "protocol_tau_err": float(protocol["tau_err"]),
        "clean_fit": clean_fit,
        "ood_fit": ood_fit,
        "anchor_checks": checks,
        "teacher_clean_by_pair": teacher_clean_by_pair,
        "teacher_pert_by_key_row": teacher_pert_by_key_row,
    }


def budget_eval_for_score(
    name: str,
    score: np.ndarray,
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    errors_h5: np.ndarray,
    uniform_alloc: dict[str, Any],
) -> dict[str, Any]:
    h = allocation_by_score(anchors, anchors_by_ep, score)
    alloc = summarize_allocation(name, h, errors_h5, anchors)
    delta = paired_bootstrap_delta(
        alloc["episode_total_error"],
        uniform_alloc["episode_total_error"],
        alloc["episode_emitted_steps"],
        uniform_alloc["episode_emitted_steps"],
    )
    return {"allocation": alloc, "delta_vs_uniform": delta}


def build_budget_anchors(clean_eval_ex: dict[str, np.ndarray], clean: np.lib.npyio.NpzFile) -> tuple[list[dict[str, Any]], np.ndarray]:
    valid_h5 = clean["eval_valid"][:, H_TO_LABEL_IDX[5]].astype(bool)
    errors_h5 = clean["eval_err_at_h"][valid_h5, :5].astype(np.float64)
    anchors_arr = clean_eval_ex["anchor_ep_t0"][valid_h5]
    anchors = [
        {"episode": int(ep), "t0": int(t), "row_idx": int(i), "gap_score": 0.0}
        for i, (ep, t) in enumerate(anchors_arr)
    ]
    return anchors, errors_h5


def write_markdown(report: dict[str, Any]) -> None:
    def ci(m: dict[str, float]) -> str:
        return f"{m['observed']:.6f} [{m['ci95_low']:.6f}, {m['ci95_high']:.6f}]"

    lines = [
        "# G2N Native Ledger",
        "",
        f"- status: `{report['status']}`",
        f"- Outcome 1: **{report['outcomes']['outcome1']['verdict']}**",
        f"- Outcome 2: **{report['outcomes']['outcome2']['verdict']}**",
        f"- lambda: fail={LAMBDA_FAIL}, teacher={LAMBDA_TEACHER}, unlogged={LAMBDA_UNLOGGED}, budget={LAMBDA_BUDGET}",
        "",
        "## Clean Eval AUROC/UER",
        "",
        "| arm | h=1 AUROC | h=1 UER | h=5 AUROC | h=5 UER |",
        "|---|---:|---:|---:|---:|",
    ]
    for arm in ("D", "E", "F", "G", "H"):
        m1 = report["arms"][arm]["clean_eval"]["h1_q75"]
        m5 = report["arms"][arm]["clean_eval"]["h5_q75"]
        lines.append(
            f"| `{arm}` | {ci(m1['failure_detection_auroc'])} | {ci(m1['unlogged_error_rate'])} | "
            f"{ci(m5['failure_detection_auroc'])} | {ci(m5['unlogged_error_rate'])} |"
        )
    lines.extend(["", "## Budget Delta", "", "| allocation score | delta observed | 95% CI | verdict |", "|---|---:|---:|---|"])
    for arm in ("F", "G", "H", "oracle"):
        d = report["budget_allocation"][arm]["delta_vs_uniform"]
        verdict = "positive" if d["ci95_high"] < 0 else "not_positive"
        lines.append(f"| `{arm}` | {d['observed']:.9f} | [{d['ci95_low']:.9f}, {d['ci95_high']:.9f}] | {verdict} |")
    lines.extend(
        [
            "",
            "## Outcome Rules",
            "",
            f"- Outcome 1 improved iff F clean eval h=1 AUROC observed >= {OUTCOME1_C_OBS}.",
            f"- Outcome 1 robust-win-kept iff F clean eval h=1 AUROC CI separates from B={OUTCOME1_B_OBS}.",
            "- Outcome 2 positive iff F budget delta CI is entirely below 0.",
            "",
            "## Not Claimed",
            "",
            "- single checkpoint, single export",
            "- lambda values were not tuned or scanned",
            "- no planning or control benefit is claimed; budget allocation is prediction budget only",
            "- perturb eval future-token cache is absent, so perturb eval uses masked zero future tokens",
            "",
        ]
    )
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    require_inputs()
    np.random.seed(PYTHON_SEED)
    torch.manual_seed(TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
    REPORT_DIR.mkdir(exist_ok=True)

    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    rows = flatten_transition_rows(data)
    pair_row = pair_to_row_index(rows)
    pair_for_row = row_index_to_pair(rows)
    splits = split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")

    clean = np.load(CLEAN_LABELS)
    pert = np.load(PERT_LABELS)
    horizon_report = json.loads(HORIZON_JSON.read_text(encoding="utf-8"))
    phase2c_report = json.loads(PHASE2C_JSON.read_text(encoding="utf-8"))
    lat_ood_report = json.loads(LAT_OOD_AWARE_JSON.read_text(encoding="utf-8"))

    parts_by_key, train_pert_keys = load_phase2c_perturb_train_parts(phase2c_report)
    pert_eval_keys = [str(k) for k in pert["slice_keys"].tolist()]
    teachers = rebuild_teachers(data, rows, parts_by_key, train_pert_keys)

    clean_train_ex = build_clean_examples(data, clean, "train", teachers["teacher_clean_by_pair"])
    clean_eval_ex = build_clean_examples(data, clean, "eval", None)
    pert_train_ex = build_perturbed_examples(
        data,
        clean["tau"][0].astype(np.float64),
        pair_for_row,
        parts_by_key,
        teachers["teacher_pert_by_key_row"],
        split="train",
        keys=train_pert_keys,
        labels=None,
    )

    train_sets = {
        "D": clean_train_ex,
        "E": clean_train_ex,
        "F": concat_examples([clean_train_ex, pert_train_ex]),
        "G": concat_examples([clean_train_ex, pert_train_ex]),
        "H": concat_examples([clean_train_ex, pert_train_ex]),
    }
    configs = {
        "D": dict(include_future=False, action_only=False, use_teacher=True, use_unlogged=False, use_budget=False, label_permutation_seed=None),
        "E": dict(include_future=True, action_only=False, use_teacher=False, use_unlogged=False, use_budget=False, label_permutation_seed=None),
        "F": dict(include_future=True, action_only=False, use_teacher=True, use_unlogged=True, use_budget=True, label_permutation_seed=None),
        "G": dict(include_future=True, action_only=True, use_teacher=True, use_unlogged=True, use_budget=True, label_permutation_seed=None),
        "H": dict(include_future=True, action_only=False, use_teacher=True, use_unlogged=True, use_budget=True, label_permutation_seed=MATCHED_RANDOM_SEED),
    }

    arms: dict[str, Any] = {}
    models: dict[str, NativeLedgerTransformer] = {}
    norms: dict[str, dict[str, np.ndarray]] = {}
    clean_logits: dict[str, np.ndarray] = {}
    for arm in ("D", "E", "F", "G", "H"):
        print(f"[train] arm={arm} rows={len(train_sets[arm]['episode'])}", flush=True)
        model, info, norm = train_arm(arm, train_sets[arm], **configs[arm])
        models[arm] = model
        norms[arm] = norm
        logits = predict_logits(model, clean_eval_ex, norm)
        clean_logits[arm] = logits
        arms[arm] = {
            "info": info,
            "clean_eval": evaluate_clean(logits, clean_eval_ex),
        }

    print("[eval] OOD slices", flush=True)
    for arm in ("D", "E", "F", "G", "H"):
        arms[arm]["ood_eval"] = evaluate_ood(models[arm], norms[arm], data, pert, pert_eval_keys)

    anchors, errors_h5 = build_budget_anchors(clean_eval_ex, clean)
    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        anchors_by_ep[int(anchor["episode"])].append(i)
    uniform_h = allocation_uniform(anchors_by_ep)
    uniform_alloc = summarize_allocation("uniform", uniform_h, errors_h5, anchors)
    budget: dict[str, Any] = {"uniform": {"allocation": uniform_alloc}}
    valid_h5 = clean["eval_valid"][:, H_TO_LABEL_IDX[5]].astype(bool)
    for arm in ("F", "G", "H"):
        score = clean_logits[arm][valid_h5, output_col(5, 75)]
        budget[arm] = budget_eval_for_score(arm, score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_score = np.mean(errors_h5, axis=1)
    budget["oracle"] = budget_eval_for_score("oracle", oracle_score, anchors, anchors_by_ep, errors_h5, uniform_alloc)

    f_h1 = arms["F"]["clean_eval"]["h1_q75"]["failure_detection_auroc"]
    improved = bool(f_h1["observed"] >= OUTCOME1_C_OBS)
    robust = bool(f_h1["ci95_low"] > OUTCOME1_B_OBS)
    outcome1_verdict = "improved_and_robust_win_kept" if improved and robust else (
        "improved_only" if improved else "not_improved"
    )
    f_delta = budget["F"]["delta_vs_uniform"]
    outcome2_positive = bool(f_delta["ci95_high"] < 0.0)
    outcome2_verdict = "positive" if outcome2_positive else "negative_or_inconclusive"

    report = {
        "status": "ok",
        "schema_id": "g2n.horizon_aware_native_ledger",
        "protocol": {
            "seeds": {"numpy": PYTHON_SEED, "torch": TORCH_SEED, "split": SPLIT_SEED, "bootstrap": BOOTSTRAP_SEED},
            "bootstrap_resamples": BOOTSTRAPS,
            "primary_quantile": 75,
            "lambda": {
                "fail": LAMBDA_FAIL,
                "teacher": LAMBDA_TEACHER,
                "unlogged": LAMBDA_UNLOGGED,
                "budget": LAMBDA_BUDGET,
            },
            "epochs": EPOCHS,
            "batch": BATCH,
            "optimizer": "AdamW",
            "lr": LR,
            "architecture": {
                "past_tokens": WINDOW,
                "max_future_tokens": MAX_FUTURE_TOKENS,
                "d_model": D_MODEL,
                "heads": N_HEADS,
                "layers": N_LAYERS,
                "outputs": [f"h{h}_q{q}" for h in HORIZONS for q in QUANTILES],
            },
            "perturb_eval_future_tokens": "absent from g2n_labels_perturbed.npz; evaluated as zero+masked future tokens",
            "budget_rule": {
                "uniform": f"h={UNIFORM_H} for every anchor",
                "score_sorted": f"low score half h={LOW_H}, high score half h={HIGH_H}, odd median h={MID_H}",
            },
        },
        "precursors": {
            "clean_npz": str(CLEAN_LABELS),
            "perturbed_npz": str(PERT_LABELS),
            "horizon_json_status": horizon_report.get("status"),
        },
        "teacher": {
            "source": "_phase2c_ood_aware_gap.materialize_clean_split + fit_gap_head_for_parts",
            "anchor_checks": teachers["anchor_checks"],
            "clean_fit": teachers["clean_fit"],
            "ood_fit": teachers["ood_fit"],
        },
        "references": {
            "C_lewm_ledger_aware_transformer_ood_aware_h1_auroc": lat_ood_report["arms"]["lat_ood_aware"]["clean_eval"]["metrics"]["failure_detection_auroc"],
            "C_protocol_observed_threshold": OUTCOME1_C_OBS,
            "C_protocol_ci": list(OUTCOME1_C_CI),
            "B_lewm_ood_aware_gap_ood_aware_clean_eval_auroc": phase2c_report["arms"]["ood_aware"]["clean_eval"]["metrics_episode_bootstrap"]["failure_detection_auroc"],
            "B_protocol_observed_threshold": OUTCOME1_B_OBS,
        },
        "training_sets": {
            arm: {
                "rows": int(len(train_sets[arm]["episode"])),
                "clean_rows": int(np.sum(train_sets[arm]["kind"] == 0)),
                "perturbed_rows": int(np.sum(train_sets[arm]["kind"] == 1)),
            }
            for arm in train_sets
        },
        "arms": arms,
        "budget_allocation": budget,
        "outcomes": {
            "outcome1": {
                "verdict": outcome1_verdict,
                "improved_observed_ge_C": improved,
                "robust_win_kept_ci_low_gt_B": robust,
                "F_h1_q75_auroc": f_h1,
                "rule": "F observed >= 0.721 is improved; CI separated from B=0.602 is robust-win-kept",
            },
            "outcome2": {
                "verdict": outcome2_verdict,
                "positive": outcome2_positive,
                "F_delta_ledger_minus_uniform": f_delta,
                "rule": "positive iff paired episode-bootstrap CI for delta=ledger-uniform is entirely < 0",
            },
        },
        "not_claimed": [
            "single checkpoint, single export",
            "lambda values were not tuned or scanned",
            "no planning or control benefit",
            "budget allocation is prediction budget only",
        ],
    }
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(clean_json(report))
    print(json.dumps(clean_json(report["outcomes"]), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()
