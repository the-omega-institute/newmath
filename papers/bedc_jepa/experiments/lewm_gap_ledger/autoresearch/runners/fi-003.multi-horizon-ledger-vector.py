#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn as nn


ROOT = Path(__file__).resolve().parents[2]
NPZ_PATH = ROOT / "tworooms_latent_large.npz"

HYPOTHESIS_ID = "fi-003.multi-horizon-ledger-vector"
METRIC = "horizon_vector_auroc_gain"
PAST_HORIZONS = (1, 2, 4, 8, 16)
PRIMARY_H = 16
PRIMARY_Q = 75.0
SPLIT_SEED = 1701
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
EPOCHS = 240
BATCH = 64
LR = 2.0e-3
WEIGHT_DECAY = 1.0e-4


FEATURE_AUDIT = {
    "scalar": [
        (
            "past_gap_mean_cap_h16",
            "mean(prediction_mse[max(0,t-16):t]); excludes the target interval "
            "prediction_mse[t:t+16] used to define the label, so it is an "
            "already-settled pre-anchor ledger signal rather than target-horizon "
            "ground-truth error or a monotone transform of target_err.",
        )
    ],
    "vector": [
        (
            "past_gap_mean_cap_h1",
            "prediction_mse[t-1:t] only; it is before the anchor and does not "
            "include any target-horizon error used in target_err.",
        ),
        (
            "past_gap_mean_cap_h2",
            "mean(prediction_mse[max(0,t-2):t]) only; it is historical ledger "
            "state, not the future target-horizon ground truth.",
        ),
        (
            "past_gap_mean_cap_h4",
            "mean(prediction_mse[max(0,t-4):t]) only; it cannot be a monotone "
            "transform of target_err because target_err is computed from "
            "disjoint future indices t..t+15.",
        ),
        (
            "past_gap_mean_cap_h8",
            "mean(prediction_mse[max(0,t-8):t]) only; the window ends before "
            "the target label window starts.",
        ),
        (
            "past_gap_mean_cap_h16",
            "mean(prediction_mse[max(0,t-16):t]) only; this is the same legal "
            "scalar baseline signal embedded in the vector and still excludes "
            "prediction_mse[t:t+16].",
        ),
    ],
}


def set_determinism(seed: int) -> None:
    os.environ["PYTHONHASHSEED"] = str(seed)
    os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)


def split_episodes(n_ep: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(SPLIT_SEED)
    perm = rng.permutation(n_ep)
    n_train = int(round(0.60 * n_ep))
    n_cal = int(round(0.20 * n_ep))
    return {
        "train": np.sort(perm[:n_train]),
        "calibration": np.sort(perm[n_train : n_train + n_cal]),
        "eval": np.sort(perm[n_train + n_cal :]),
    }


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
        ranks[order[i:j]] = (i + 1 + j) / 2.0
        i = j
    return float((ranks[y].sum() - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg))


def sigmoid_np(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


def load_npz(path: Path) -> dict[str, np.ndarray]:
    raw = np.load(path, allow_pickle=False)
    return {k: raw[k] for k in raw.files}


def valid_transition_count(transition_mask: np.ndarray, ep: int) -> int:
    return int(transition_mask[ep].astype(bool).sum())


def build_rows(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    mse = data["prediction_mse"].astype(np.float64)
    tm = data["transition_mask"].astype(bool)
    episodes: list[int] = []
    steps: list[int] = []
    x_vector: list[list[float]] = []
    x_scalar: list[list[float]] = []
    target_err: list[float] = []

    for ep in range(tm.shape[0]):
        valid_count = valid_transition_count(tm, ep)
        for t_raw in np.where(tm[ep])[0]:
            t = int(t_raw)
            if t < 1 or t + PRIMARY_H > valid_count:
                continue

            # Feature audit:
            # - All reader inputs below are past, already-settled gap-ledger
            #   summaries over prediction_mse[max(0, t-h):t].
            # - The label is defined from target_err =
            #   mean(prediction_mse[t:t+PRIMARY_H]).
            # - These index ranges are disjoint, so no feature contains the
            #   target-horizon ground-truth error or a monotone transform of it.
            # - The scalar baseline receives only h=16 past_gap_mean; the vector
            #   reader receives the same signal across 1/2/4/8/16 past horizons.
            row = [float(np.mean(mse[ep, max(0, t - h) : t])) for h in PAST_HORIZONS]
            scalar = [row[-1]]
            truth = float(np.mean(mse[ep, t : t + PRIMARY_H]))
            if not (np.all(np.isfinite(row)) and np.isfinite(truth)):
                continue
            episodes.append(ep)
            steps.append(t)
            x_vector.append(row)
            x_scalar.append(scalar)
            target_err.append(truth)

    if not x_vector:
        raise RuntimeError("no valid non-leaking horizon rows were constructed")

    return {
        "episode": np.asarray(episodes, dtype=np.int64),
        "t": np.asarray(steps, dtype=np.int64),
        "x_vector": np.asarray(x_vector, dtype=np.float64),
        "x_scalar": np.asarray(x_scalar, dtype=np.float64),
        "target_err": np.asarray(target_err, dtype=np.float64),
    }


class Reader(nn.Module):
    def __init__(self, width: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(width, 16),
            nn.ReLU(),
            nn.Linear(16, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def standardize_by_train(x: np.ndarray, train_mask: np.ndarray) -> np.ndarray:
    mean = x[train_mask].mean(axis=0)
    scale = x[train_mask].std(axis=0)
    scale[scale < 1e-8] = 1.0
    return (x - mean) / scale


def train_reader(x: np.ndarray, y: np.ndarray, seed: int, device: torch.device) -> Reader:
    torch.manual_seed(seed)
    model = Reader(x.shape[1]).to(device)
    x_t = torch.from_numpy(x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y.astype(np.float32)).to(device)
    pos = float(y.sum())
    neg = float(len(y) - y.sum())
    pos_weight = torch.tensor([neg / max(pos, 1.0)], dtype=torch.float32, device=device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    generator = torch.Generator(device="cpu").manual_seed(seed + 1009)

    model.train()
    for _ in range(EPOCHS):
        order = torch.randperm(len(y), generator=generator)
        for start in range(0, len(y), BATCH):
            idx = order[start : start + BATCH].to(device)
            logits = model(x_t[idx])
            loss = nn.functional.binary_cross_entropy_with_logits(logits, y_t[idx], pos_weight=pos_weight)
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite reader loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()

    return model.eval()


def predict_reader(model: Reader, x: np.ndarray, device: torch.device) -> np.ndarray:
    out: list[np.ndarray] = []
    with torch.inference_mode():
        for lo in range(0, len(x), BATCH):
            hi = min(lo + BATCH, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            logits = model(xb).detach().cpu().numpy().astype(np.float64)
            out.append(logits)
            if device.type == "cuda":
                torch.cuda.empty_cache()
    return sigmoid_np(np.concatenate(out))


def fit_and_score(
    x_train: np.ndarray,
    y_train: np.ndarray,
    x_eval: np.ndarray,
    seed: int,
    device: torch.device,
) -> np.ndarray:
    model = train_reader(x_train, y_train, seed, device)
    return predict_reader(model, x_eval, device)


def paired_bootstrap_gain_by_episode(
    y: np.ndarray,
    vector_score: np.ndarray,
    scalar_score: np.ndarray,
    episode: np.ndarray,
    seed: int,
) -> dict[str, float]:
    vector_obs = auroc_rank(y, vector_score)
    scalar_obs = auroc_rank(y, scalar_score)
    observed = float(vector_obs - scalar_obs)

    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    values = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in sampled])
        values[i] = auroc_rank(y[idx], vector_score[idx]) - auroc_rank(y[idx], scalar_score[idx])
    return {
        "observed": observed,
        "low": float(np.nanpercentile(values, 2.5)),
        "high": float(np.nanpercentile(values, 97.5)),
        "vector_auroc": float(vector_obs),
        "scalar_auroc": float(scalar_obs),
    }


def clean_json(v: Any) -> Any:
    if isinstance(v, dict):
        return {str(k): clean_json(val) for k, val in v.items()}
    if isinstance(v, (list, tuple)):
        return [clean_json(val) for val in v]
    if isinstance(v, np.ndarray):
        return clean_json(v.tolist())
    if isinstance(v, np.integer):
        return int(v)
    if isinstance(v, np.floating):
        v = float(v)
    if isinstance(v, float) and not math.isfinite(v):
        return None
    return v


def make_claim(metric: dict[str, float], status: str, single_class: bool) -> str:
    if single_class:
        return (
            "tworooms latent 上去除 target-horizon label 泄漏后，eval 或 train 为单类，"
            "向量 vs 单标量的配对 AUROC 增益不可识别并 fail-closed。"
        )
    return (
        "tworooms latent 上已去除 target-horizon label 泄漏；多 horizon past-gap ledger "
        f"向量 vs 单 horizon 标量的配对 AUROC 增益为 {metric['observed']:.6f}, "
        f"95% CI=[{metric['low']:.6f},{metric['high']:.6f}] "
        f"(vector AUROC={metric['vector_auroc']:.6f}, scalar AUROC={metric['scalar_auroc']:.6f})，"
        f"delta_ci_above_zero 判据结论为 {status}。"
    )


def make_payload(seed: int) -> dict[str, Any]:
    set_determinism(seed)
    data = load_npz(NPZ_PATH)
    rows = build_rows(data)
    splits = split_episodes(int(data["emb"].shape[0]))

    train_mask = np.isin(rows["episode"], splits["train"])
    eval_mask = np.isin(rows["episode"], splits["eval"])
    target_err = rows["target_err"]
    tau = float(np.percentile(target_err[train_mask], PRIMARY_Q))
    y = (target_err > tau).astype(np.int8)

    train_y = y[train_mask]
    eval_y = y[eval_mask]
    single_class = np.unique(train_y).size < 2 or np.unique(eval_y).size < 2

    if single_class:
        metric = {"observed": 0.0, "low": 0.0, "high": 0.0, "vector_auroc": 0.5, "scalar_auroc": 0.5}
        status = "fail-closed"
    else:
        x_vector = standardize_by_train(rows["x_vector"], train_mask)
        x_scalar = standardize_by_train(rows["x_scalar"], train_mask)
        device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
        try:
            vector_score = fit_and_score(x_vector[train_mask], train_y, x_vector[eval_mask], seed + 11, device)
            scalar_score = fit_and_score(x_scalar[train_mask], train_y, x_scalar[eval_mask], seed + 29, device)
        except RuntimeError as exc:
            if device.type != "cuda" or "deterministic" not in str(exc).lower():
                raise
            torch.cuda.empty_cache()
            device = torch.device("cpu")
            vector_score = fit_and_score(x_vector[train_mask], train_y, x_vector[eval_mask], seed + 11, device)
            scalar_score = fit_and_score(x_scalar[train_mask], train_y, x_scalar[eval_mask], seed + 29, device)
        metric = paired_bootstrap_gain_by_episode(
            eval_y,
            vector_score,
            scalar_score,
            rows["episode"][eval_mask],
            seed + BOOTSTRAP_SEED_OFFSET,
        )
        if metric["low"] > 0.0:
            status = "positive"
        elif metric["high"] <= 0.0:
            status = "negative"
        else:
            status = "unidentifiable"
        if torch.cuda.is_available():
            torch.cuda.empty_cache()

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": float(metric["observed"]),
        "ci": {"low": float(metric["low"]), "high": float(metric["high"])},
        "measured_scope": [METRIC, "auroc"],
        "reported_claim": make_claim(metric, status, single_class),
    }
    if single_class or status == "unidentifiable":
        payload["status"] = "fail-closed"
    return clean_json(payload)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    payload = make_payload(args.seed)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")), encoding="utf-8")


if __name__ == "__main__":
    main()
