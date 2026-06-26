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
import torch.nn.functional as F


ROOT = Path(__file__).resolve().parents[2]
NPZ_PATH = ROOT / "tworooms_latent_large.npz"

HYPOTHESIS_ID = "fi-008.native-ledger-objective"
METRIC = "ledger_minus_plain_mse"
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159

WINDOW = 6
HIDDEN = 256
LAYERS = 2
EPOCHS = 120
BATCH_SIZE = 512
LR = 7.0e-4
WEIGHT_DECAY = 1.0e-4
LEDGER_WEIGHT = 0.25
MODEL_SEED_OFFSET = 8808
ORDER_SEED_OFFSET = 50000


@dataclass(frozen=True)
class PreparedData:
    win_emb_train: np.ndarray
    win_act_train: np.ndarray
    next_train: np.ndarray
    win_emb_eval: np.ndarray
    win_act_eval: np.ndarray
    next_eval: np.ndarray
    episode_eval: np.ndarray
    lewm_mse_eval: np.ndarray
    emb_mean: np.ndarray
    emb_scale: np.ndarray
    act_mean: np.ndarray
    act_scale: np.ndarray
    anchor_identity_max_abs: float
    eval_episode_count: int


class WindowPredictor(nn.Module):
    """Same-size native predictor used for both arms.

    The dynamics head predicts normalized next latent. The ledger head predicts
    the model's own detached normalized one-step error on train batches.
    """

    def __init__(self, emb_dim: int, act_dim: int) -> None:
        super().__init__()
        in_dim = WINDOW * (emb_dim + act_dim)
        blocks: list[nn.Module] = []
        cur = in_dim
        for _ in range(LAYERS):
            blocks.append(nn.Linear(cur, HIDDEN))
            blocks.append(nn.GELU())
            cur = HIDDEN
        self.trunk = nn.Sequential(*blocks)
        self.dynamics_head = nn.Linear(cur, emb_dim)
        self.ledger_head = nn.Linear(cur, 1)

    def forward(self, win_emb: torch.Tensor, win_act: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        x = torch.cat([win_emb, win_act], dim=-1).flatten(start_dim=1)
        h = self.trunk(x)
        return self.dynamics_head(h), self.ledger_head(h).squeeze(-1)


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


def train_standardizer(a: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    flat = a.reshape(-1, a.shape[-1])
    mean = flat.mean(axis=0, dtype=np.float64).astype(np.float32)
    scale = flat.std(axis=0, dtype=np.float64).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(a: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((a - mean) / scale).astype(np.float32)


def build_windows(
    emb: np.ndarray,
    action: np.ndarray,
    transition_mask: np.ndarray,
) -> dict[str, np.ndarray]:
    ep_idx, t_idx = np.where(transition_mask.astype(bool))
    n = len(ep_idx)
    emb_dim = int(emb.shape[-1])
    act_dim = int(action.shape[-1])
    win_emb = np.empty((n, WINDOW, emb_dim), dtype=np.float32)
    win_act = np.empty((n, WINDOW, act_dim), dtype=np.float32)
    for i, (ep_raw, t_raw) in enumerate(zip(ep_idx, t_idx)):
        ep = int(ep_raw)
        t = int(t_raw)
        for w in range(WINDOW):
            src = max(0, t - WINDOW + 1 + w)
            win_emb[i, w] = emb[ep, src]
            win_act[i, w] = action[ep, src]
    return {
        "episode": ep_idx.astype(np.int64),
        "t": t_idx.astype(np.int64),
        "win_emb": win_emb,
        "win_act": win_act,
        "next_emb": emb[ep_idx, t_idx + 1].astype(np.float32),
    }


def prepare_data(seed: int) -> PreparedData:
    with np.load(NPZ_PATH, allow_pickle=False) as raw:
        emb = raw["emb"].astype(np.float32)
        action = raw["action"].astype(np.float32)
        transition_mask = raw["transition_mask"].astype(bool)
        transition_target_emb = raw["transition_target_emb"].astype(np.float32)
        lewm_mse = raw["prediction_mse"].astype(np.float64)

    rows = build_windows(emb, action, transition_mask)
    train_ep, eval_ep = split_episodes(int(emb.shape[0]), seed)
    train_mask = np.isin(rows["episode"], train_ep)
    eval_mask = np.isin(rows["episode"], eval_ep)

    lewm_row_mse = lewm_mse[rows["episode"], rows["t"]]
    finite = (
        np.isfinite(rows["win_emb"]).all(axis=(1, 2))
        & np.isfinite(rows["win_act"]).all(axis=(1, 2))
        & np.isfinite(rows["next_emb"]).all(axis=1)
        & np.isfinite(lewm_row_mse)
    )
    train_mask = train_mask & finite
    eval_mask = eval_mask & finite

    if int(train_mask.sum()) == 0 or int(eval_mask.sum()) == 0:
        raise RuntimeError("empty train/eval transition split")

    emb_mean, emb_scale = train_standardizer(rows["win_emb"][train_mask])
    act_mean, act_scale = train_standardizer(rows["win_act"][train_mask])

    target_ref = emb[:, 1:, :]
    anchor_identity_max_abs = float(np.max(np.abs(transition_target_emb[transition_mask] - target_ref[transition_mask])))

    return PreparedData(
        win_emb_train=apply_standardizer(rows["win_emb"][train_mask], emb_mean, emb_scale),
        win_act_train=apply_standardizer(rows["win_act"][train_mask], act_mean, act_scale),
        next_train=apply_standardizer(rows["next_emb"][train_mask], emb_mean, emb_scale),
        win_emb_eval=apply_standardizer(rows["win_emb"][eval_mask], emb_mean, emb_scale),
        win_act_eval=apply_standardizer(rows["win_act"][eval_mask], act_mean, act_scale),
        next_eval=rows["next_emb"][eval_mask].astype(np.float32),
        episode_eval=rows["episode"][eval_mask].astype(np.int64),
        lewm_mse_eval=lewm_row_mse[eval_mask].astype(np.float64),
        emb_mean=emb_mean,
        emb_scale=emb_scale,
        act_mean=act_mean,
        act_scale=act_scale,
        anchor_identity_max_abs=anchor_identity_max_abs,
        eval_episode_count=int(len(np.unique(rows["episode"][eval_mask]))),
    )


def fit_predictor(
    data: PreparedData,
    *,
    seed: int,
    device: torch.device,
    use_ledger_loss: bool,
) -> np.ndarray:
    model_seed = seed + MODEL_SEED_OFFSET
    torch.manual_seed(model_seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(model_seed)

    emb_dim = int(data.win_emb_train.shape[-1])
    act_dim = int(data.win_act_train.shape[-1])
    model = WindowPredictor(emb_dim=emb_dim, act_dim=act_dim).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    x_emb_t = torch.from_numpy(data.win_emb_train).to(device)
    x_act_t = torch.from_numpy(data.win_act_train).to(device)
    y_t = torch.from_numpy(data.next_train).to(device)
    generator = torch.Generator(device="cpu").manual_seed(seed + ORDER_SEED_OFFSET)

    model.train()
    n = int(len(data.win_emb_train))
    for _epoch in range(EPOCHS):
        order = torch.randperm(n, generator=generator)
        for lo in range(0, n, BATCH_SIZE):
            idx = order[lo : lo + BATCH_SIZE].to(device)
            pred_norm, ledger_log = model(x_emb_t[idx], x_act_t[idx])
            per_row_mse = torch.mean((pred_norm - y_t[idx]) ** 2, dim=1)
            pred_loss = torch.mean(per_row_mse)
            loss = pred_loss
            if use_ledger_loss:
                target_gap = torch.log1p(per_row_mse.detach())
                ledger_loss = F.smooth_l1_loss(ledger_log, target_gap)
                loss = loss + LEDGER_WEIGHT * ledger_loss
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite native predictor loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()

    pred_parts: list[np.ndarray] = []
    model.eval()
    with torch.inference_mode():
        for lo in range(0, len(data.win_emb_eval), 1024):
            hi = min(lo + 1024, len(data.win_emb_eval))
            xb = torch.from_numpy(data.win_emb_eval[lo:hi]).to(device)
            ab = torch.from_numpy(data.win_act_eval[lo:hi]).to(device)
            pred_norm, _ledger_log = model(xb, ab)
            pred_parts.append(pred_norm.detach().cpu().numpy().astype(np.float32))

    pred_norm_np = np.concatenate(pred_parts, axis=0)
    pred_next = pred_norm_np * data.emb_scale + data.emb_mean
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return pred_next.astype(np.float32)


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


def build_claim(plain_mse: float, ledger_mse: float, lewm_mse: float, metric: dict[str, float], verdict: str) -> str:
    gain = clean_float(float(plain_mse - ledger_mse))
    if gain > 0.0:
        gap_text = f"ledger 目标把 native-vs-LeWM gap 缩小 {fmt(gain)}"
    elif gain < 0.0:
        gap_text = f"ledger 目标把 native-vs-LeWM gap 扩大 {fmt(-gain)}"
    else:
        gap_text = "ledger 目标未改变 native-vs-LeWM gap"
    return (
        f"plain_mse={fmt(plain_mse)}, ledger_mse={fmt(ledger_mse)}, "
        f"lewm_mse={fmt(lewm_mse)}, gain_plain_minus_ledger={fmt(gain)}, "
        f"ledger_minus_plain_mse={fmt(metric['observed'])}, "
        f"95% CI=[{fmt(metric['low'])},{fmt(metric['high'])}], "
        f"delta_ci_below_zero={verdict}; {gap_text}。"
    )


def build_payload(seed: int) -> dict[str, Any]:
    device = configure_determinism(seed)
    data = prepare_data(seed)

    plain_pred = fit_predictor(data, seed=seed, device=device, use_ledger_loss=False)
    ledger_pred = fit_predictor(data, seed=seed, device=device, use_ledger_loss=True)

    plain_step_mse = per_step_mse(plain_pred, data.next_eval)
    ledger_step_mse = per_step_mse(ledger_pred, data.next_eval)
    plain_mse = clean_float(float(plain_step_mse.mean()))
    ledger_mse = clean_float(float(ledger_step_mse.mean()))
    lewm_mse = clean_float(float(data.lewm_mse_eval.mean()))

    metric = episode_bootstrap_delta_ci(
        ledger_step_mse - plain_step_mse,
        data.episode_eval,
        seed=seed + BOOTSTRAP_SEED_OFFSET,
    )
    verdict = verdict_from_delta_ci(metric["low"], metric["high"])

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": data.anchor_identity_max_abs},
        "metric": METRIC,
        "metric_value": metric["observed"],
        "ci": {"low": metric["low"], "high": metric["high"]},
        "measured_scope": [METRIC, "mse"],
        "reported_claim": build_claim(plain_mse, ledger_mse, lewm_mse, metric, verdict),
    }

    if data.anchor_identity_max_abs != 0.0:
        payload["status"] = "fail-closed"
        payload["metric_value"] = 0.0
        payload["ci"] = {"low": 0.0, "high": 0.0}
        payload["reported_claim"] = "fail-closed: transition_target_emb does not match emb[t+1] exactly."
    elif data.eval_episode_count <= 1 or verdict == "unidentifiable":
        payload["status"] = "fail-closed"

    if torch.cuda.is_available():
        torch.cuda.empty_cache()
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
