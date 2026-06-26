#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn as nn


ROOT = Path(__file__).resolve().parents[2]
NPZ_PATH = ROOT / "tworooms_latent_large.npz"

HYPOTHESIS_ID = "fi-007.native-predictor-pilot"
METRIC = "native_minus_trivial_mse"
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
BATCH_SIZE = 512


@dataclass(frozen=True)
class PredictorConfig:
    name: str
    hidden: int
    layers: int
    epochs: int
    lr: float
    weight_decay: float
    seed_offset: int


SMALL_CONFIG = PredictorConfig(
    name="small",
    hidden=128,
    layers=1,
    epochs=200,
    lr=8.0e-4,
    weight_decay=1.0e-4,
    seed_offset=1101,
)

LARGE_CONFIG = PredictorConfig(
    name="large",
    hidden=256,
    layers=2,
    epochs=80,
    lr=5.0e-4,
    weight_decay=1.0e-3,
    seed_offset=2202,
)


@dataclass(frozen=True)
class PreparedData:
    x_train: np.ndarray
    delta_train: np.ndarray
    x_eval: np.ndarray
    y_eval: np.ndarray
    episode_eval: np.ndarray
    lewm_mse_eval: np.ndarray
    anchor_identity_max_abs: float
    eval_episode_count: int


class ResidualMlp(nn.Module):
    def __init__(self, dim: int, hidden: int, layers: int) -> None:
        super().__init__()
        blocks: list[nn.Module] = []
        in_dim = dim
        for _ in range(layers):
            blocks.append(nn.Linear(in_dim, hidden))
            blocks.append(nn.GELU())
            in_dim = hidden
        blocks.append(nn.Linear(in_dim, dim))
        self.net = nn.Sequential(*blocks)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


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
        raise ValueError(f"non-finite payload float: {out!r}")
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


def split_episodes(n_episodes: int, seed: int) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    perm = rng.permutation(n_episodes)
    n_train = int(round(0.60 * n_episodes))
    n_cal = int(round(0.20 * n_episodes))
    train = np.sort(perm[:n_train])
    eval_ep = np.sort(perm[n_train + n_cal :])
    return train, eval_ep


def standardize(
    train: np.ndarray,
    eval_arr: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    mean = train.mean(axis=0, dtype=np.float64).astype(np.float32)
    scale = train.std(axis=0, dtype=np.float64).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return (
        ((train - mean) / scale).astype(np.float32),
        ((eval_arr - mean) / scale).astype(np.float32),
        mean,
        scale,
    )


def prepare_data(seed: int) -> PreparedData:
    with np.load(NPZ_PATH, allow_pickle=False) as raw:
        emb = raw["emb"].astype(np.float32)
        transition_mask = raw["transition_mask"].astype(bool)
        transition_target_emb = raw["transition_target_emb"].astype(np.float32)
        lewm_mse = raw["prediction_mse"].astype(np.float64)

    ep_idx, t_idx = np.where(transition_mask)
    train_ep, eval_ep = split_episodes(int(emb.shape[0]), seed)
    train_mask = np.isin(ep_idx, train_ep)
    eval_mask = np.isin(ep_idx, eval_ep)

    x = emb[ep_idx, t_idx].astype(np.float32)
    y = emb[ep_idx, t_idx + 1].astype(np.float32)
    delta = (y - x).astype(np.float32)

    target_ref = emb[:, 1:, :]
    anchor_identity_max_abs = float(np.max(np.abs(transition_target_emb[transition_mask] - target_ref[transition_mask])))

    finite = (
        np.isfinite(x).all(axis=1)
        & np.isfinite(y).all(axis=1)
        & np.isfinite(delta).all(axis=1)
        & np.isfinite(lewm_mse[ep_idx, t_idx])
    )
    train_mask = train_mask & finite
    eval_mask = eval_mask & finite

    x_train = x[train_mask]
    delta_train = delta[train_mask]
    x_eval = x[eval_mask]
    y_eval = y[eval_mask]
    episode_eval = ep_idx[eval_mask].astype(np.int64)
    lewm_mse_eval = lewm_mse[ep_idx[eval_mask], t_idx[eval_mask]].astype(np.float64)

    if len(x_train) == 0 or len(x_eval) == 0:
        raise RuntimeError("empty train/eval transition split")

    return PreparedData(
        x_train=x_train,
        delta_train=delta_train,
        x_eval=x_eval,
        y_eval=y_eval,
        episode_eval=episode_eval,
        lewm_mse_eval=lewm_mse_eval,
        anchor_identity_max_abs=anchor_identity_max_abs,
        eval_episode_count=int(len(np.unique(episode_eval))),
    )


def fit_predictor(
    cfg: PredictorConfig,
    data: PreparedData,
    *,
    seed: int,
    device: torch.device,
) -> tuple[np.ndarray, dict[str, float | int | str]]:
    x_train, x_eval_std, x_mean, x_scale = standardize(data.x_train, data.x_eval)
    delta_train, _unused, delta_mean, delta_scale = standardize(data.delta_train, data.delta_train[:1])
    _ = _unused

    model_seed = seed + cfg.seed_offset
    torch.manual_seed(model_seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(model_seed)

    dim = int(data.x_train.shape[1])
    model = ResidualMlp(dim=dim, hidden=cfg.hidden, layers=cfg.layers).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=cfg.lr, weight_decay=cfg.weight_decay)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    delta_t = torch.from_numpy(delta_train.astype(np.float32)).to(device)
    generator = torch.Generator(device="cpu").manual_seed(seed + cfg.seed_offset + 50000)

    model.train()
    optimizer_steps = 0
    for _epoch in range(cfg.epochs):
        order = torch.randperm(len(x_train), generator=generator)
        for lo in range(0, len(x_train), BATCH_SIZE):
            idx = order[lo : lo + BATCH_SIZE].to(device)
            pred_delta = model(x_t[idx])
            loss = nn.functional.mse_loss(pred_delta, delta_t[idx])
            if not torch.isfinite(loss):
                raise RuntimeError(f"non-finite loss in {cfg.name} predictor")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
            optimizer_steps += 1

    pred_delta_parts: list[np.ndarray] = []
    model.eval()
    with torch.inference_mode():
        for lo in range(0, len(data.x_eval), 1024):
            hi = min(lo + 1024, len(data.x_eval))
            xb = torch.from_numpy(x_eval_std[lo:hi].astype(np.float32)).to(device)
            pred_delta_parts.append(model(xb).detach().cpu().numpy().astype(np.float32))
    pred_delta_std = np.concatenate(pred_delta_parts, axis=0)
    pred_delta = pred_delta_std * delta_scale + delta_mean
    pred_next = data.x_eval + pred_delta.astype(np.float32)

    if device.type == "cuda":
        torch.cuda.empty_cache()

    info: dict[str, float | int | str] = {
        "name": cfg.name,
        "hidden": int(cfg.hidden),
        "layers": int(cfg.layers),
        "epochs": int(cfg.epochs),
        "lr": float(cfg.lr),
        "weight_decay": float(cfg.weight_decay),
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "optimizer_steps": int(optimizer_steps),
        "device": str(device),
    }
    _ = x_mean, x_scale
    return pred_next.astype(np.float32), info


def per_step_mse(pred: np.ndarray, target: np.ndarray) -> np.ndarray:
    return np.mean((pred.astype(np.float64) - target.astype(np.float64)) ** 2, axis=1)


def episode_bootstrap_delta_ci(
    delta: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
) -> dict[str, float]:
    observed = clean_float(float(delta.mean()))
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    samples = np.empty(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        chosen = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in chosen])
        samples[i] = float(delta[idx].mean())
    return {
        "observed": observed,
        "low": clean_float(float(np.percentile(samples, 2.5))),
        "high": clean_float(float(np.percentile(samples, 97.5))),
    }


def verdict_from_delta_ci(low: float, high: float) -> str:
    if high < 0.0:
        return "positive"
    if low >= 0.0:
        return "negative"
    return "unidentifiable"


def fmt(value: float) -> str:
    return f"{clean_float(value):.6f}"


def build_payload(seed: int) -> dict[str, Any]:
    device = configure_determinism(seed)
    data = prepare_data(seed)

    small_pred, small_info = fit_predictor(SMALL_CONFIG, data, seed=seed, device=device)
    large_pred, large_info = fit_predictor(LARGE_CONFIG, data, seed=seed, device=device)

    trivial_pred = data.x_eval
    small_mse = per_step_mse(small_pred, data.y_eval)
    large_mse = per_step_mse(large_pred, data.y_eval)
    trivial_mse = per_step_mse(trivial_pred, data.y_eval)

    small_native = clean_float(float(small_mse.mean()))
    large_native = clean_float(float(large_mse.mean()))
    trivial = clean_float(float(trivial_mse.mean()))
    lewm = clean_float(float(data.lewm_mse_eval.mean()))
    ratio = clean_float(float(large_native / lewm))
    small_ratio = clean_float(float(small_native / lewm))
    small_gap = clean_float(float(small_native - lewm))
    large_gap = clean_float(float(large_native - lewm))
    gap_delta = clean_float(float(large_gap - small_gap))

    metric_delta = large_mse - trivial_mse
    metric = episode_bootstrap_delta_ci(
        metric_delta,
        data.episode_eval,
        seed=seed + BOOTSTRAP_SEED_OFFSET,
    )
    verdict = verdict_from_delta_ci(metric["low"], metric["high"])

    if gap_delta < 0.0:
        scaling = f"larger narrowed native-LeWM gap by {fmt(-gap_delta)}"
    elif gap_delta > 0.0:
        scaling = f"larger widened native-LeWM gap by {fmt(gap_delta)}"
    else:
        scaling = "larger left native-LeWM gap unchanged"

    reported_claim = (
        f"large native_mse={fmt(large_native)}, trivial_mse={fmt(trivial)}, "
        f"lewm_mse={fmt(lewm)}, ratio={fmt(ratio)}; "
        f"small native_mse={fmt(small_native)} ratio={fmt(small_ratio)}, {scaling}."
    )

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": data.anchor_identity_max_abs},
        "metric": METRIC,
        "metric_value": metric["observed"],
        "ci": {"low": metric["low"], "high": metric["high"]},
        "measured_scope": [METRIC, "mse"],
        "reported_claim": reported_claim,
    }

    if data.anchor_identity_max_abs != 0.0:
        payload["status"] = "fail-closed"
        payload["metric_value"] = 0.0
        payload["ci"] = {"low": 0.0, "high": 0.0}
        payload["reported_claim"] = "fail-closed: transition_target_emb does not match emb[t+1] exactly."
    elif data.eval_episode_count <= 1 or verdict == "unidentifiable":
        payload["status"] = "fail-closed"

    _ = small_info, large_info
    return clean_json(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, help="Path to write the frozen JSON payload.")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = build_payload(int(args.seed))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    if torch.cuda.is_available():
        torch.cuda.empty_cache()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
