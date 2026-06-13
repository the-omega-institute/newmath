from __future__ import annotations

import argparse
import json
import math
import os
import random
from collections import defaultdict
from pathlib import Path
from typing import Any

os.environ.setdefault("CUBLAS_WORKSPACE_CONFIG", ":4096:8")

import numpy as np
import torch
import torch.nn as nn


ROOT = Path(__file__).resolve().parents[2]
PUSHT_NPZ = ROOT / "pusht_latent_large.npz"
PUSHT_LABELS = ROOT / "reports" / "crossenv_horizon_labels_pusht.npz"

HISTORY = 6
TARGET_H = 5
UNIFORM_H = 3
LOW_H = 5
MID_H = 3
HIGH_H = 1
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
ANCHOR_TOL = 1e-4


def finite_json(v: Any) -> Any:
    if isinstance(v, dict):
        return {str(k): finite_json(val) for k, val in v.items()}
    if isinstance(v, (list, tuple)):
        return [finite_json(val) for val in v]
    if isinstance(v, np.ndarray):
        return finite_json(v.tolist())
    if isinstance(v, (np.integer,)):
        return int(v)
    if isinstance(v, (np.floating,)):
        v = float(v)
    if isinstance(v, float) and not math.isfinite(v):
        return None
    return v


def configure_determinism(seed: int) -> torch.device:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    torch.set_num_threads(1)
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")


def load_npz(path: Path) -> dict[str, np.ndarray]:
    raw = np.load(path, allow_pickle=False)
    return {k: raw[k] for k in raw.files}


def h1_identity_anchor(data: dict[str, np.ndarray], labels: dict[str, np.ndarray]) -> float:
    max_abs = 0.0
    for split in ("train", "calibration", "eval"):
        anchors = labels[f"{split}_anchor_ep_t0"].astype(np.int64)
        valid = labels[f"{split}_valid"][:, 0].astype(bool)
        h1 = labels[f"{split}_err_at_h"][:, 0].astype(np.float64)
        ref = np.asarray([data["prediction_mse"][int(ep), int(t)] for ep, t in anchors], dtype=np.float64)
        if np.any(valid):
            max_abs = max(max_abs, float(np.max(np.abs(ref[valid] - h1[valid]))))
    return max_abs


def make_features(data: dict[str, np.ndarray], anchors: np.ndarray) -> np.ndarray:
    emb = data["emb"].astype(np.float32)
    act = data["action"].astype(np.float32)
    mse = data["prediction_mse"].astype(np.float32)
    transition_mask = data["transition_mask"].astype(bool)
    n, emb_dim = len(anchors), emb.shape[-1]
    act_dim = act.shape[-1]
    out = np.zeros((n, HISTORY * (emb_dim + act_dim) + 5), dtype=np.float32)
    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t = int(t_raw)
        chunks: list[np.ndarray] = []
        for w in range(HISTORY):
            src = max(0, t - HISTORY + 1 + w)
            z = emb[ep, src]
            a = act[ep, src]
            z = np.where(np.isfinite(z), z, 0.0).astype(np.float32)
            a = np.where(np.isfinite(a), a, 0.0).astype(np.float32)
            chunks.extend([z, a])
        valid_transition_count = int(transition_mask[ep].sum())
        denom = float(max(1, valid_transition_count - 1))
        prev_mse = np.asarray(
            [
                mse[ep, max(0, t - 2)],
                mse[ep, max(0, t - 1)],
                mse[ep, t],
                float(t) / denom,
                float(valid_transition_count) / float(max(1, transition_mask.shape[1])),
            ],
            dtype=np.float32,
        )
        prev_mse = np.where(np.isfinite(prev_mse), prev_mse, 0.0).astype(np.float32)
        chunks.append(prev_mse)
        out[i] = np.concatenate(chunks, axis=0)
    return out


def normalize_features(x_train: np.ndarray, x_eval: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = x_train.mean(axis=0, dtype=np.float64).astype(np.float32)
    scale = x_train.std(axis=0, dtype=np.float64).astype(np.float32)
    scale[scale < 1e-6] = 1.0
    return ((x_train - mean) / scale).astype(np.float32), ((x_eval - mean) / scale).astype(np.float32)


def train_targets(labels: dict[str, np.ndarray]) -> tuple[float, dict[str, np.ndarray]]:
    valid = labels["train_valid"][:, :TARGET_H].all(axis=1)
    h5_valid = labels["train_valid"][:, TARGET_H - 1].astype(bool)
    mean_h5 = labels["train_mean_err_to_h"][:, TARGET_H - 1].astype(np.float64)
    tau = float(np.percentile(mean_h5[h5_valid], 75))
    err5 = labels["train_err_at_h"][:, :TARGET_H].astype(np.float64)
    cvar_tail = np.max(err5, axis=1)
    fail = ((mean_h5 > tau) & valid & np.isfinite(mean_h5)).astype(np.float32)
    tail_threshold = float(np.percentile(cvar_tail[valid & (fail > 0)], 75)) if np.any(valid & (fail > 0)) else float("inf")
    tail_fail = ((fail > 0) & (cvar_tail >= tail_threshold) & np.isfinite(cvar_tail)).astype(np.float32)
    return tau, {"valid": valid, "fail": fail, "tail_fail": tail_fail, "cvar_tail": cvar_tail}


class MlpHead(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, 64),
            nn.ReLU(),
            nn.Linear(64, 32),
            nn.ReLU(),
            nn.Linear(32, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def fit_head(
    x: np.ndarray,
    y: np.ndarray,
    tail_fail: np.ndarray,
    *,
    seed: int,
    device: torch.device,
    cvar_weight: float,
) -> MlpHead:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = MlpHead(x.shape[1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=1e-3, weight_decay=1e-4)
    x_t = torch.from_numpy(x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y.astype(np.float32)).to(device)
    tail_t = torch.from_numpy(tail_fail.astype(np.float32)).to(device)
    generator = torch.Generator(device="cpu").manual_seed(seed)
    batch = 128
    model.train()
    for _ in range(60):
        order = torch.randperm(len(y), generator=generator)
        for start in range(0, len(y), batch):
            idx = order[start : start + batch].to(device)
            logits = model(x_t[idx])
            per = nn.functional.binary_cross_entropy_with_logits(logits, y_t[idx], reduction="none")
            weights = 1.0 + cvar_weight * tail_t[idx]
            loss = (per * weights).mean()
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite training loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


def predict_head(model: MlpHead, x: np.ndarray, device: torch.device) -> np.ndarray:
    out = np.zeros(len(x), dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, len(x), 512):
            hi = min(lo + 512, len(x))
            batch = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            out[lo:hi] = model(batch).detach().cpu().numpy().astype(np.float64)
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


def summarize_allocation(h: np.ndarray, errors_h5: np.ndarray, anchors: np.ndarray) -> dict[str, dict[str, float] | dict[str, int]]:
    anchor_error = np.asarray([float(errors_h5[i, : int(h_i)].sum()) for i, h_i in enumerate(h)], dtype=np.float64)
    err_by_ep: dict[str, float] = defaultdict(float)
    steps_by_ep: dict[str, int] = defaultdict(int)
    for i, (ep_raw, _) in enumerate(anchors):
        ep = str(int(ep_raw))
        err_by_ep[ep] += float(anchor_error[i])
        steps_by_ep[ep] += int(h[i])
    return {
        "episode_total_error": {k: float(err_by_ep[k]) for k in sorted(err_by_ep, key=int)},
        "episode_emitted_steps": {k: int(steps_by_ep[k]) for k in sorted(steps_by_ep, key=int)},
    }


def paired_delta(
    arm_a: dict[str, dict[str, float] | dict[str, int]],
    arm_b: dict[str, dict[str, float] | dict[str, int]],
    *,
    seed: int,
) -> dict[str, float]:
    a_err = arm_a["episode_total_error"]
    b_err = arm_b["episode_total_error"]
    a_steps = arm_a["episode_emitted_steps"]
    b_steps = arm_b["episode_emitted_steps"]
    eps = sorted(b_err.keys(), key=int)  # type: ignore[union-attr]
    if eps != sorted(a_err.keys(), key=int):  # type: ignore[union-attr]
        raise RuntimeError("episode keys differ")
    a_e = np.asarray([a_err[ep] for ep in eps], dtype=np.float64)  # type: ignore[index]
    b_e = np.asarray([b_err[ep] for ep in eps], dtype=np.float64)  # type: ignore[index]
    a_s = np.asarray([a_steps[ep] for ep in eps], dtype=np.float64)  # type: ignore[index]
    b_s = np.asarray([b_steps[ep] for ep in eps], dtype=np.float64)  # type: ignore[index]
    observed = float(a_e.sum() / a_s.sum() - b_e.sum() / b_s.sum())
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        idx = rng.integers(0, len(eps), size=len(eps))
        samples[i] = float(a_e[idx].sum() / a_s[idx].sum() - b_e[idx].sum() / b_s[idx].sum())
    return {
        "observed": observed,
        "ci95_low": float(np.percentile(samples, 2.5)),
        "ci95_high": float(np.percentile(samples, 97.5)),
    }


def build_payload(seed: int) -> dict[str, Any]:
    device = configure_determinism(seed)
    data = load_npz(PUSHT_NPZ)
    labels = load_npz(PUSHT_LABELS)
    anchor_value = h1_identity_anchor(data, labels)
    if not (math.isfinite(anchor_value) and anchor_value < ANCHOR_TOL):
        return {
            "hypothesis_id": "fi-001.cvar-tail",
            "anchor": {"field": "anchor.identity_max_abs", "value": anchor_value},
            "metric": "allocation_delta",
            "metric_value": 0.0,
            "ci": {"low": 0.0, "high": 0.0},
            "status": "fail-closed",
            "measured_scope": ["allocation_delta"],
            "reported_claim": "PushT 标签 identity anchor 未通过，未报告 CVaR allocation delta。",
        }

    tau, targets = train_targets(labels)
    train_valid = targets["valid"].astype(bool)
    train_anchors = labels["train_anchor_ep_t0"][train_valid].astype(np.int64)
    eval_valid = labels["eval_valid"][:, :TARGET_H].all(axis=1)
    eval_anchors = labels["eval_anchor_ep_t0"][eval_valid].astype(np.int64)
    errors_h5 = labels["eval_err_at_h"][eval_valid, :TARGET_H].astype(np.float64)
    train_y = targets["fail"][train_valid].astype(np.float32)
    train_tail = targets["tail_fail"][train_valid].astype(np.float32)

    if np.unique(train_y).size < 2:
        single_class = True
    else:
        eval_mean_h5 = labels["eval_mean_err_to_h"][eval_valid, TARGET_H - 1].astype(np.float64)
        eval_y = (eval_mean_h5 > tau).astype(np.int8)
        single_class = bool(np.unique(eval_y).size < 2)

    if single_class or len(eval_anchors) == 0:
        return {
            "hypothesis_id": "fi-001.cvar-tail",
            "anchor": {"field": "anchor.identity_max_abs", "value": float(anchor_value)},
            "metric": "allocation_delta",
            "metric_value": 0.0,
            "ci": {"low": 0.0, "high": 0.0},
            "status": "fail-closed",
            "measured_scope": ["allocation_delta"],
            "reported_claim": "PushT h5 失败标签在 train/eval 中单类或无有效 eval anchor，allocation delta 不可识别。",
        }

    x_train_raw = make_features(data, train_anchors)
    x_eval_raw = make_features(data, eval_anchors)
    x_train, x_eval = normalize_features(x_train_raw, x_eval_raw)

    baseline = fit_head(x_train, train_y, train_tail, seed=seed + 17, device=device, cvar_weight=0.0)
    cvar = fit_head(x_train, train_y, train_tail, seed=seed + 17, device=device, cvar_weight=3.0)
    baseline_score = predict_head(baseline, x_eval, device)
    cvar_score = predict_head(cvar, x_eval, device)

    by_ep = anchors_by_episode(eval_anchors)
    baseline_alloc = summarize_allocation(allocation_by_score(eval_anchors, by_ep, baseline_score), errors_h5, eval_anchors)
    cvar_alloc = summarize_allocation(allocation_by_score(eval_anchors, by_ep, cvar_score), errors_h5, eval_anchors)
    delta = paired_delta(cvar_alloc, baseline_alloc, seed=seed + BOOTSTRAP_SEED_OFFSET)

    claim: str
    if delta["ci95_high"] < 0.0:
        claim = "在 PushT latent 的固定 episode bootstrap 下，CVaR 尾部加权臂的 allocation_delta CI 严格低于 0。"
    elif delta["ci95_low"] >= 0.0:
        claim = "在 PushT latent 的固定 episode bootstrap 下，CVaR 尾部加权臂未优于 baseline，allocation_delta CI 不低于 0。"
    else:
        claim = "在 PushT latent 的固定 episode bootstrap 下，CVaR 尾部加权臂相对 baseline 的 allocation_delta 跨 0，不可识别为改进。"

    return {
        "hypothesis_id": "fi-001.cvar-tail",
        "anchor": {"field": "anchor.identity_max_abs", "value": float(anchor_value)},
        "metric": "allocation_delta",
        "metric_value": float(delta["observed"]),
        "ci": {"low": float(delta["ci95_low"]), "high": float(delta["ci95_high"])},
        "measured_scope": ["allocation_delta"],
        "reported_claim": claim,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    payload = finite_json(build_payload(args.seed))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
