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
SOURCE_NPZ = ROOT / "tworooms_latent_large.npz"
TARGET_NPZ = ROOT / "reacher_latent_large.npz"

HYPOTHESIS_ID = "fi-009.reader-fewshot-transfer"
METRIC = "fewshot_transfer_auroc"
ZERO_SHOT_FI004_AUROC = 0.43

PRIMARY_H = 16
PRIMARY_Q = 75.0
PAST_HORIZONS = (1, 2, 4, 8, 16)
FEWSHOT_K = 10

BOOTSTRAPS = 500
BATCH = 128
SOURCE_EPOCHS = 320
FEWSHOT_EPOCHS = 180
LR = 1.0e-3
FEWSHOT_LR = 3.0e-4
WEIGHT_DECAY = 1.0e-4
EPS = 1.0e-12

FEATURE_AUDIT = (
    (
        "log_past_gap_mean_h1",
        "log(mean(prediction_mse[t-1:t]) + eps); only settled pre-anchor "
        "predictor error, disjoint from label window prediction_mse[t:t+16].",
    ),
    (
        "log_past_gap_mean_h2",
        "log(mean(prediction_mse[max(0,t-2):t]) + eps); historical gap only, "
        "no target-horizon ground-truth error.",
    ),
    (
        "log_past_gap_mean_h4",
        "log(mean(prediction_mse[max(0,t-4):t]) + eps); the feature interval "
        "ends exactly before the label interval begins.",
    ),
    (
        "log_past_gap_mean_h8",
        "log(mean(prediction_mse[max(0,t-8):t]) + eps); only pre-anchor "
        "ledger self-error summary.",
    ),
    (
        "log_past_gap_mean_h16",
        "log(mean(prediction_mse[max(0,t-16):t]) + eps); same legal "
        "lookback in tworooms and reacher, never prediction_mse[t:t+16].",
    ),
    (
        "log_ratio_h1_to_h16",
        "log((past_gap_mean_h1 + eps) / (past_gap_mean_h16 + eps)); derived "
        "only from pre-anchor gap summaries.",
    ),
    (
        "log_ratio_h4_to_h16",
        "log((past_gap_mean_h4 + eps) / (past_gap_mean_h16 + eps)); "
        "scale-relative pre-anchor history, not a target label transform.",
    ),
    (
        "past_gap_cv_h16",
        "std(prediction_mse[max(0,t-16):t]) / mean(...); pre-anchor history "
        "shape, disjoint from prediction_mse[t:t+16].",
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

            # Non-leakage invariant for every feature:
            # - Reader inputs use prediction_mse[max(0, t-h):t], which is
            #   fully before the anchor t.
            # - The label uses mean(prediction_mse[t:t+16]).
            # - Feature and label intervals are index-disjoint.
            means: list[float] = []
            for h in PAST_HORIZONS:
                start = max(0, t - h)
                if not bool(np.all(tm[ep, start:t])):
                    means = []
                    break
                means.append(float(np.mean(mse[ep, start:t])))
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
        raise RuntimeError("no legal few-shot transfer rows were constructed")

    return {
        "episode": np.asarray(episodes, dtype=np.int64),
        "t": np.asarray(steps, dtype=np.int64),
        "x": np.asarray(features, dtype=np.float64),
        "target_err": np.asarray(target_err, dtype=np.float64),
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


def standardizer(x_source_train: np.ndarray, x_fewshot_train: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    # The scaler uses only training data: source train plus the allowed K
    # target train episodes. Reacher eval is never inspected here.
    train_only = np.concatenate([x_source_train, x_fewshot_train], axis=0)
    mean = train_only.mean(axis=0)
    scale = train_only.std(axis=0)
    scale[scale < 1.0e-8] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return (x - mean) / scale


def bce_pos_weight(y: np.ndarray, device: torch.device) -> torch.Tensor:
    pos = float(y.sum())
    neg = float(len(y) - y.sum())
    return torch.tensor([neg / max(pos, 1.0)], dtype=torch.float32, device=device)


def train_epochs(
    model: Reader,
    x: np.ndarray,
    y: np.ndarray,
    *,
    epochs: int,
    lr: float,
    seed: int,
    device: torch.device,
) -> None:
    x_t = torch.from_numpy(x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y.astype(np.float32)).to(device)
    pos_weight = bce_pos_weight(y, device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=WEIGHT_DECAY)
    generator = torch.Generator(device="cpu").manual_seed(seed + 1009)

    model.train()
    for _ in range(epochs):
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
    model.eval()


def train_fewshot_reader(
    x_source: np.ndarray,
    y_source: np.ndarray,
    x_fewshot: np.ndarray,
    y_fewshot: np.ndarray,
    seed: int,
    device: torch.device,
) -> Reader:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = Reader(x_source.shape[1]).to(device)
    train_epochs(model, x_source, y_source, epochs=SOURCE_EPOCHS, lr=LR, seed=seed + 11, device=device)
    train_epochs(
        model,
        x_fewshot,
        y_fewshot,
        epochs=FEWSHOT_EPOCHS,
        lr=FEWSHOT_LR,
        seed=seed + 29,
        device=device,
    )
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


def make_claim(metric: dict[str, float], status: str, k: int, eval_episode_count: int) -> str:
    relation = "above" if metric["observed"] > ZERO_SHOT_FI004_AUROC else "not above"
    return (
        f"K={k} reacher train episodes fine-tuned after tworooms pretraining; "
        f"held-out reacher eval ({eval_episode_count} episodes) fewshot_transfer_auroc="
        f"{metric['observed']:.12g}, 95% CI=[{metric['low']:.12g},{metric['high']:.12g}], "
        f"vs fi-004 zero-shot AUROC about {ZERO_SHOT_FI004_AUROC:.2f} ({relation} zero-shot). "
        f"Null 0.5 CI criterion is {status}; scope limited to the listed measured fields."
    )


def make_payload(seed: int) -> dict[str, Any]:
    set_determinism(seed)
    source_data = load_npz(SOURCE_NPZ)
    target_data = load_npz(TARGET_NPZ)
    source_rows = build_rows(source_data)
    target_rows = build_rows(target_data)

    source_splits = split_episodes(int(source_data["emb"].shape[0]), seed)
    target_splits = split_episodes(int(target_data["emb"].shape[0]), seed)
    fewshot_episodes = np.sort(target_splits["train"][:FEWSHOT_K])

    source_train_mask = np.isin(source_rows["episode"], source_splits["train"])
    target_train_mask = np.isin(target_rows["episode"], target_splits["train"])
    fewshot_mask = np.isin(target_rows["episode"], fewshot_episodes)
    target_eval_mask = np.isin(target_rows["episode"], target_splits["eval"])

    if (
        int(source_train_mask.sum()) == 0
        or int(target_train_mask.sum()) == 0
        or int(fewshot_mask.sum()) == 0
        or int(target_eval_mask.sum()) == 0
    ):
        return fail_closed_payload(
            f"K={FEWSHOT_K} few-shot transfer AUROC is unidentifiable because a required split has zero anchors."
        )

    source_tau = float(np.percentile(source_rows["target_err"][source_train_mask], PRIMARY_Q))
    # The target failure threshold is calibrated on the same K legal target
    # train episodes used for fine-tuning; no remaining target train episodes
    # and no target eval rows are inspected for this few-shot label boundary.
    target_tau = float(np.percentile(target_rows["target_err"][fewshot_mask], PRIMARY_Q))
    y_source = (source_rows["target_err"] > source_tau).astype(np.int8)
    y_target = (target_rows["target_err"] > target_tau).astype(np.int8)
    y_source_train = y_source[source_train_mask]
    y_fewshot = y_target[fewshot_mask]
    y_eval = y_target[target_eval_mask]

    if np.unique(y_source_train).size < 2 or np.unique(y_fewshot).size < 2 or np.unique(y_eval).size < 2:
        return fail_closed_payload(
            f"K={FEWSHOT_K} few-shot transfer AUROC is unidentifiable because source, few-shot, or reacher eval labels are single-class."
        )

    mean, scale = standardizer(source_rows["x"][source_train_mask], target_rows["x"][fewshot_mask])
    x_source_train = apply_standardizer(source_rows["x"][source_train_mask], mean, scale)
    x_fewshot = apply_standardizer(target_rows["x"][fewshot_mask], mean, scale)
    x_eval = apply_standardizer(target_rows["x"][target_eval_mask], mean, scale)

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    try:
        model = train_fewshot_reader(x_source_train, y_source_train, x_fewshot, y_fewshot, seed + 11, device)
        score = predict_reader(model, x_eval, device)
    except RuntimeError as exc:
        if device.type != "cuda" or "deterministic" not in str(exc).lower():
            raise
        if torch.cuda.is_available():
            torch.cuda.empty_cache()
        device = torch.device("cpu")
        model = train_fewshot_reader(x_source_train, y_source_train, x_fewshot, y_fewshot, seed + 11, device)
        score = predict_reader(model, x_eval, device)

    metric = bootstrap_auroc_by_episode(
        y_eval,
        score,
        target_rows["episode"][target_eval_mask],
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
        "reported_claim": make_claim(
            metric,
            status,
            FEWSHOT_K,
            int(np.unique(target_rows["episode"][target_eval_mask]).size),
        ),
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
