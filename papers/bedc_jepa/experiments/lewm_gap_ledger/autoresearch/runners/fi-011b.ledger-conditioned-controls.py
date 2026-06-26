#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import random
import sys
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


ROOT = Path(__file__).resolve().parents[2]
BASE_RUNNER = Path(__file__).resolve().with_name("fi-008.native-ledger-objective.py")
NPZ_PATH = ROOT / "tworooms_latent_large.npz"

HYPOTHESIS_ID = "fi-011b.ledger-conditioned-controls"
METRIC = "conditioned_minus_constant_mse"

BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
WINDOW = 6
HIDDEN = 256
LAYERS = 2
EPOCHS = 80
BATCH_SIZE = 512
LR = 6.0e-4
WEIGHT_DECAY = 1.0e-4
LEDGER_WEIGHT = 0.20
ORDER_SEED_OFFSET = 51000


def load_base() -> Any:
    spec = importlib.util.spec_from_file_location("_fi008_base", BASE_RUNNER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


base = load_base()


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


class CapacityMatchedFiLMPredictor(nn.Module):
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
        self.ledger_head = nn.Linear(cur, 1)
        self.film = nn.Linear(1, 2 * cur)
        self.dynamics_head = nn.Linear(cur, emb_dim)

    def forward(
        self,
        win_emb: torch.Tensor,
        win_act: torch.Tensor,
        *,
        mode: str,
        generator: torch.Generator | None = None,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        x = torch.cat([win_emb, win_act], dim=-1).flatten(start_dim=1)
        h = self.trunk(x)
        ledger = self.ledger_head(h)
        if mode == "conditioned":
            cond = ledger
        elif mode == "constant":
            cond = torch.zeros_like(ledger)
        elif mode == "shuffled":
            if ledger.shape[0] <= 1:
                cond = ledger.detach()
            else:
                perm = torch.randperm(ledger.shape[0], generator=generator, device=ledger.device)
                cond = ledger.detach()[perm]
        elif mode == "plain":
            cond = None
        else:
            raise ValueError(f"unknown mode: {mode}")
        if cond is not None:
            gamma_beta = self.film(cond)
            gamma, beta = gamma_beta.chunk(2, dim=-1)
            h = h * (1.0 + 0.10 * torch.tanh(gamma)) + 0.10 * torch.tanh(beta)
        return self.dynamics_head(h), ledger.squeeze(-1)


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


def fit_predictor(
    data: Any,
    *,
    seed: int,
    device: torch.device,
    mode: str,
) -> tuple[np.ndarray, dict[str, Any]]:
    model_seed = seed + 11000 + {"plain": 1, "constant": 2, "conditioned": 3, "shuffled": 4}[mode]
    torch.manual_seed(model_seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(model_seed)

    emb_dim = int(data.win_emb_train.shape[-1])
    act_dim = int(data.win_act_train.shape[-1])
    model = CapacityMatchedFiLMPredictor(emb_dim=emb_dim, act_dim=act_dim).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    x_emb_t = torch.from_numpy(data.win_emb_train).to(device)
    x_act_t = torch.from_numpy(data.win_act_train).to(device)
    y_t = torch.from_numpy(data.next_train).to(device)
    order_generator = torch.Generator(device="cpu").manual_seed(seed + ORDER_SEED_OFFSET + model_seed)
    shuffle_generator = torch.Generator(device=device).manual_seed(seed + 70000 + model_seed)

    model.train()
    n = int(len(data.win_emb_train))
    optimizer_steps = 0
    for _epoch in range(EPOCHS):
        order = torch.randperm(n, generator=order_generator)
        for lo in range(0, n, BATCH_SIZE):
            idx = order[lo : lo + BATCH_SIZE].to(device)
            pred_norm, ledger_log = model(x_emb_t[idx], x_act_t[idx], mode=mode, generator=shuffle_generator)
            per_row_mse = torch.mean((pred_norm - y_t[idx]) ** 2, dim=1)
            pred_loss = torch.mean(per_row_mse)
            target_gap = torch.log1p(per_row_mse.detach())
            ledger_loss = F.smooth_l1_loss(ledger_log, target_gap)
            loss = pred_loss + LEDGER_WEIGHT * ledger_loss
            if not torch.isfinite(loss):
                raise RuntimeError(f"non-finite loss in {mode}")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
            optimizer_steps += 1

    pred_parts: list[np.ndarray] = []
    model.eval()
    with torch.inference_mode():
        for lo in range(0, len(data.win_emb_eval), 1024):
            hi = min(lo + 1024, len(data.win_emb_eval))
            xb = torch.from_numpy(data.win_emb_eval[lo:hi]).to(device)
            ab = torch.from_numpy(data.win_act_eval[lo:hi]).to(device)
            pred_norm, _ledger_log = model(xb, ab, mode=mode, generator=shuffle_generator)
            pred_parts.append(pred_norm.detach().cpu().numpy().astype(np.float32))

    pred_norm_np = np.concatenate(pred_parts, axis=0)
    pred_next = pred_norm_np * data.emb_scale + data.emb_mean
    info = {
        "mode": mode,
        "hidden": HIDDEN,
        "layers": LAYERS,
        "epochs": EPOCHS,
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "optimizer_steps": int(optimizer_steps),
        "device": str(device),
    }
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return pred_next.astype(np.float32), info


def per_step_mse(pred: np.ndarray, target: np.ndarray) -> np.ndarray:
    return np.mean((pred.astype(np.float64) - target.astype(np.float64)) ** 2, axis=1)


def episode_bootstrap_delta_ci(delta: np.ndarray, episode: np.ndarray, *, seed: int) -> dict[str, float]:
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


def make_fail_payload(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": [METRIC, "mse", "capacity_matched_controls"],
        "reported_claim": f"fail-closed: {reason}",
    }


def build_claim(mse: dict[str, float], metric: dict[str, float], controls: dict[str, dict[str, float]], verdict: str) -> str:
    return (
        f"capacity-matched ledger-conditioning controls: conditioned_mse={fmt(mse['conditioned'])}, "
        f"constant_mse={fmt(mse['constant'])}, plain_mse={fmt(mse['plain'])}, "
        f"shuffled_mse={fmt(mse['shuffled'])}, conditioned_minus_constant_mse={fmt(metric['observed'])}, "
        f"95% CI=[{fmt(metric['low'])},{fmt(metric['high'])}], criterion={verdict}; "
        f"conditioned_minus_plain={fmt(controls['conditioned_minus_plain']['observed'])}, "
        f"conditioned_minus_shuffled={fmt(controls['conditioned_minus_shuffled']['observed'])}. "
        "All arms share the same trunk, FiLM module, ledger head, split, and next-latent target; controls test whether the conditioning signal, not parameter count alone, carries the effect."
    )


def build_payload(seed: int) -> dict[str, Any]:
    if not NPZ_PATH.exists():
        return make_fail_payload(f"missing carrier {NPZ_PATH.name}")
    device = configure_determinism(seed)
    data = base.prepare_data(seed)
    if data.anchor_identity_max_abs != 0.0:
        return make_fail_payload("transition_target_emb does not match emb[t+1] exactly")

    preds: dict[str, np.ndarray] = {}
    infos: dict[str, dict[str, Any]] = {}
    for mode in ("plain", "constant", "conditioned", "shuffled"):
        pred, info = fit_predictor(data, seed=seed, device=device, mode=mode)
        preds[mode] = pred
        infos[mode] = info

    step_mse = {mode: per_step_mse(pred, data.next_eval) for mode, pred in preds.items()}
    mse = {mode: clean_float(float(values.mean())) for mode, values in step_mse.items()}
    metric = episode_bootstrap_delta_ci(
        step_mse["conditioned"] - step_mse["constant"],
        data.episode_eval,
        seed=seed + BOOTSTRAP_SEED_OFFSET,
    )
    controls = {
        "conditioned_minus_plain": episode_bootstrap_delta_ci(
            step_mse["conditioned"] - step_mse["plain"],
            data.episode_eval,
            seed=seed + BOOTSTRAP_SEED_OFFSET + 11,
        ),
        "conditioned_minus_shuffled": episode_bootstrap_delta_ci(
            step_mse["conditioned"] - step_mse["shuffled"],
            data.episode_eval,
            seed=seed + BOOTSTRAP_SEED_OFFSET + 23,
        ),
    }
    verdict = verdict_from_delta_ci(metric["low"], metric["high"])
    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": data.anchor_identity_max_abs},
        "metric": METRIC,
        "metric_value": metric["observed"],
        "ci": {"low": metric["low"], "high": metric["high"]},
        "measured_scope": [METRIC, "mse", "capacity_matched_controls", "shuffled_ledger_control"],
        "reported_claim": build_claim(mse, metric, controls, verdict),
        "diagnostics": {
            "mse": mse,
            "controls": controls,
            "model_info": infos,
            "eval_episode_count": int(data.eval_episode_count),
        },
    }
    if data.eval_episode_count <= 1 or verdict == "unidentifiable":
        payload["status"] = "fail-closed"
    if torch.cuda.is_available():
        torch.cuda.empty_cache()
    return clean_json(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    payload = build_payload(int(args.seed))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
