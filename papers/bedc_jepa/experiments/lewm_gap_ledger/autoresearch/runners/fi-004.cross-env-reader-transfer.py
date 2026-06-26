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
TRAIN_NPZ = ROOT / "tworooms_latent_large.npz"
EVAL_NPZ = ROOT / "reacher_latent_large.npz"

HYPOTHESIS_ID = "fi-004.cross-env-reader-transfer"
METRIC = "transfer_auroc"
PRIMARY_H = 16
PRIMARY_Q = 75.0
PAST_HORIZONS = (1, 2, 4, 8, 16)
BOOTSTRAPS = 500
BATCH = 128
EPOCHS = 320
LR = 1.0e-3
WEIGHT_DECAY = 1.0e-4
EPS = 1.0e-12

FEATURE_AUDIT = (
    (
        "log_past_gap_mean_h1",
        "log(mean(prediction_mse[t-1:t]) + eps); uses only the last settled "
        "pre-anchor predictor error and excludes prediction_mse[t:t+16].",
    ),
    (
        "log_past_gap_mean_h2",
        "log(mean(prediction_mse[max(0,t-2):t]) + eps); historical gap only, "
        "with no target-horizon ground-truth error.",
    ),
    (
        "log_past_gap_mean_h4",
        "log(mean(prediction_mse[max(0,t-4):t]) + eps); the window ends before "
        "the label window starts.",
    ),
    (
        "log_past_gap_mean_h8",
        "log(mean(prediction_mse[max(0,t-8):t]) + eps); past predictor "
        "self-error summary only.",
    ),
    (
        "log_past_gap_mean_h16",
        "log(mean(prediction_mse[max(0,t-16):t]) + eps); same historical "
        "lookback used in train and eval, disjoint from prediction_mse[t:t+16].",
    ),
    (
        "log_ratio_h1_to_h16",
        "log((past_gap_mean_h1 + eps) / (past_gap_mean_h16 + eps)); a "
        "scale-relative transform of pre-anchor ledger gaps only.",
    ),
    (
        "log_ratio_h4_to_h16",
        "log((past_gap_mean_h4 + eps) / (past_gap_mean_h16 + eps)); uses only "
        "pre-anchor gap summaries.",
    ),
    (
        "past_gap_cv_h16",
        "std(prediction_mse[max(0,t-16):t]) / mean(...); pre-anchor history "
        "shape, not target-horizon error.",
    ),
)


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


def set_determinism(seed: int) -> None:
    os.environ["PYTHONHASHSEED"] = str(seed)
    os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    if hasattr(torch.backends, "cudnn"):
        torch.backends.cudnn.benchmark = False
        torch.backends.cudnn.deterministic = True
    try:
        torch.set_num_threads(1)
        torch.set_num_interop_threads(1)
    except RuntimeError:
        pass


def clean_float(value: float) -> float:
    value = float(value)
    if value == 0.0:
        return 0.0
    if not math.isfinite(value):
        raise ValueError(f"non-finite float in payload: {value!r}")
    return value


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
    if isinstance(v, float):
        return clean_float(v)
    return v


def load_npz(path: Path) -> dict[str, np.ndarray]:
    if not path.exists():
        raise FileNotFoundError(path)
    with np.load(path, allow_pickle=False) as raw:
        return {key: raw[key] for key in raw.files}


def split_episodes(n_ep: int, seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed + 1701)
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


def valid_transition_count(mask: np.ndarray, ep: int) -> int:
    return int(mask[ep].astype(bool).sum())


def build_rows(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    mse = data["prediction_mse"].astype(np.float64)
    tm = data["transition_mask"].astype(bool)
    episodes: list[int] = []
    steps: list[int] = []
    features: list[list[float]] = []
    target_err: list[float] = []

    for ep in range(tm.shape[0]):
        valid_count = valid_transition_count(tm, ep)
        for t_raw in np.where(tm[ep])[0]:
            t = int(t_raw)
            if t < 1 or t + PRIMARY_H > valid_count:
                continue
            if not bool(np.all(tm[ep, t : t + PRIMARY_H])):
                continue

            # Leak audit for every feature:
            # - Features use only prediction_mse[max(0, t-h):t], i.e. already
            #   settled predictor self-error before the anchor.
            # - The label uses target_err = mean(prediction_mse[t:t+16]).
            # - The feature windows and target window are index-disjoint.
            # - The same construction is used for tworooms train and reacher eval.
            means: list[float] = []
            for h in PAST_HORIZONS:
                start = max(0, t - h)
                if not bool(np.all(tm[ep, start:t])):
                    means = []
                    break
                past = mse[ep, start:t]
                means.append(float(np.mean(past)))
            if not means:
                continue

            past16 = mse[ep, max(0, t - 16) : t]
            truth = float(np.mean(mse[ep, t : t + PRIMARY_H]))
            row = [math.log(max(v, 0.0) + EPS) for v in means]
            row.append(math.log((means[0] + EPS) / (means[-1] + EPS)))
            row.append(math.log((means[2] + EPS) / (means[-1] + EPS)))
            row.append(float(np.std(past16) / (abs(means[-1]) + EPS)))

            if not (np.all(np.isfinite(row)) and np.isfinite(truth)):
                continue
            episodes.append(ep)
            steps.append(t)
            features.append(row)
            target_err.append(truth)

    if not features:
        raise RuntimeError("no legal cross-env gap-reader rows were constructed")

    return {
        "episode": np.asarray(episodes, dtype=np.int64),
        "t": np.asarray(steps, dtype=np.int64),
        "x": np.asarray(features, dtype=np.float64),
        "target_err": np.asarray(target_err, dtype=np.float64),
    }


def standardize_from_source_train(
    x_train: np.ndarray,
    x_eval: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    mean = x_train.mean(axis=0)
    scale = x_train.std(axis=0)
    scale[scale < 1.0e-8] = 1.0
    return (x_train - mean) / scale, (x_eval - mean) / scale


def train_reader(x: np.ndarray, y: np.ndarray, seed: int, device: torch.device) -> Reader:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
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
        for lo in range(0, len(y), BATCH):
            idx = order[lo : lo + BATCH].to(device)
            logits = model(x_t[idx])
            loss = nn.functional.binary_cross_entropy_with_logits(logits, y_t[idx], pos_weight=pos_weight)
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite reader loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    return model.eval()


def predict_reader(model: Reader, x: np.ndarray, device: torch.device) -> np.ndarray:
    scores: list[np.ndarray] = []
    with torch.inference_mode():
        for lo in range(0, len(x), BATCH):
            hi = min(lo + BATCH, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            logits = model(xb).detach().cpu().numpy().astype(np.float64)
            scores.append(logits)
            if device.type == "cuda":
                torch.cuda.empty_cache()
    return sigmoid_np(np.concatenate(scores))


def bootstrap_auroc_by_episode(
    y: np.ndarray,
    score: np.ndarray,
    episode: np.ndarray,
    seed: int,
) -> dict[str, float]:
    observed = auroc_rank(y, score)
    unique_ep = np.unique(episode)
    if unique_ep.size == 0:
        return {"observed": 0.5, "low": 0.5, "high": 0.5}
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed + 314159)
    values = np.empty(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in sampled])
        values[i] = auroc_rank(y[idx], score[idx])
    return {
        "observed": float(observed),
        "low": float(np.nanpercentile(values, 2.5)),
        "high": float(np.nanpercentile(values, 97.5)),
    }


def fail_closed_payload(claim: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.5,
        "ci": {"low": 0.5, "high": 0.5},
        "status": "fail-closed",
        "measured_scope": [METRIC, "auroc"],
        "reported_claim": claim,
    }


def make_claim(metric: dict[str, float], status: str) -> str:
    return (
        "A reader trained on tworooms pre-anchor gap history scored reacher "
        f"zero-shot transfer_auroc={metric['observed']:.12g} with 95% CI "
        f"[{metric['low']:.12g},{metric['high']:.12g}], so the null-0.5 "
        f"CI criterion is {status}."
    )


def make_payload(seed: int) -> dict[str, Any]:
    set_determinism(seed)
    train_data = load_npz(TRAIN_NPZ)
    eval_data = load_npz(EVAL_NPZ)
    train_rows = build_rows(train_data)
    eval_rows = build_rows(eval_data)

    train_splits = split_episodes(int(train_data["emb"].shape[0]), seed)
    eval_splits = split_episodes(int(eval_data["emb"].shape[0]), seed)
    source_train_mask = np.isin(train_rows["episode"], train_splits["train"])
    reacher_train_mask = np.isin(eval_rows["episode"], eval_splits["train"])
    reacher_eval_mask = np.isin(eval_rows["episode"], eval_splits["eval"])

    if int(source_train_mask.sum()) == 0 or int(reacher_train_mask.sum()) == 0 or int(reacher_eval_mask.sum()) == 0:
        return fail_closed_payload("Cross-env transfer AUROC is unidentifiable because a required split has zero anchors.")

    source_tau = float(np.percentile(train_rows["target_err"][source_train_mask], PRIMARY_Q))
    reacher_tau = float(np.percentile(eval_rows["target_err"][reacher_train_mask], PRIMARY_Q))
    y_source = (train_rows["target_err"] > source_tau).astype(np.int8)
    y_reacher = (eval_rows["target_err"] > reacher_tau).astype(np.int8)
    y_train = y_source[source_train_mask]
    y_eval = y_reacher[reacher_eval_mask]

    if np.unique(y_train).size < 2 or np.unique(y_eval).size < 2:
        return fail_closed_payload("Cross-env transfer AUROC is unidentifiable because train or reacher eval labels are single-class.")

    x_train, x_eval = standardize_from_source_train(
        train_rows["x"][source_train_mask],
        eval_rows["x"][reacher_eval_mask],
    )
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    try:
        model = train_reader(x_train, y_train, seed + 11, device)
        score = predict_reader(model, x_eval, device)
    except RuntimeError as exc:
        if device.type != "cuda":
            raise
        if torch.cuda.is_available():
            torch.cuda.empty_cache()
        device = torch.device("cpu")
        model = train_reader(x_train, y_train, seed + 11, device)
        score = predict_reader(model, x_eval, device)
        _ = exc

    metric = bootstrap_auroc_by_episode(
        y_eval,
        score,
        eval_rows["episode"][reacher_eval_mask],
        seed,
    )
    if metric["low"] > 0.5:
        status = "positive"
    elif metric["high"] <= 0.5:
        status = "negative"
    else:
        status = "unidentifiable"

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": float(metric["observed"]),
        "ci": {"low": float(metric["low"]), "high": float(metric["high"])},
        "measured_scope": [METRIC, "auroc"],
        "reported_claim": make_claim(metric, status),
    }
    if status == "unidentifiable":
        payload["status"] = "fail-closed"
    if torch.cuda.is_available():
        torch.cuda.empty_cache()
    return clean_json(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, help="Path to write the frozen verdict payload JSON.")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = make_payload(args.seed)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, ensure_ascii=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
