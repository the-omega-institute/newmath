#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn as nn


SCRIPT_PATH = Path(__file__).resolve()
SURVEY_DIR = SCRIPT_PATH.parents[2]
if str(SURVEY_DIR) not in sys.path:
    sys.path.insert(0, str(SURVEY_DIR))

from _phase1c_gap_ledger import (  # noqa: E402
    auroc_rank,
    build_gap_features,
    distinction_truth,
    fit_linear_r2_quality,
    fit_logistic_head,
    flatten_transition_rows,
    predict_logistic_head,
    split_episodes,
)


HYPOTHESIS_ID = "fi-006.reader-capacity-saturation"
METRIC = "mlp_minus_linear_auroc"
NPZ_PATH = SURVEY_DIR / "tworooms_latent_large.npz"
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
PRIMARY_PROBE_INDICES = (0,)
DISTINCTIONS = ("agent_room_right", "same_room", "near_target")
EPOCHS = 600
BATCH_SIZE = 256
LR = 1.0e-3
WEIGHT_DECAY = 1.0e-4


FEATURE_AUDIT = [
    (
        "agent_room_right_probe_probability",
        "由 train split 上的 current-anchor emb->agent_room_right probe 产生；是 predictor/distinction 自评信号，不含 prediction_mse 或 target-horizon 真误差。",
    ),
    (
        "agent_room_right_probe_logit",
        "同一 probe 的 current-anchor logit；只反映当前 latent 可分性/置信度，不读取定义 failure label 的 native prediction_mse。",
    ),
    (
        "agent_room_right_probe_prediction",
        "同一 probe 的阈值预测；truth 只在 probe 训练时来自当前位置几何，reader 输入不含 failure label 或其单调函数。",
    ),
    (
        "agent_room_right_signed_margin",
        "phase1c gap feature 中的 signed margin，即 probe logit 的自评置信度；不是 target-horizon/transition error。",
    ),
    (
        "agent_room_right_min_abs_margin",
        "phase1c gap feature 中的 min_abs_margin；单 probe B 版等于 abs(logit)，只表达自评不确定性。",
    ),
    (
        "emb_to_observation_train_r2_quality",
        "train split 拟合的 emb->observation R2 常量向量；不按 eval 样本变化，不含 failure label、eval truth 或 prediction_mse。",
    ),
]


@dataclass(frozen=True)
class PreparedData:
    x: np.ndarray
    y: np.ndarray
    episode: np.ndarray
    train_mask: np.ndarray
    eval_mask: np.ndarray


class LinearReader(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.net = nn.Linear(in_dim, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


class MlpReader(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        hidden = max(16, min(64, in_dim * 4))
        self.net = nn.Sequential(
            nn.Linear(in_dim, hidden),
            nn.ReLU(),
            nn.Linear(hidden, hidden // 2),
            nn.ReLU(),
            nn.Linear(hidden // 2, 1),
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


def load_npz_dict(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as raw:
        return {key: raw[key] for key in raw.files}


def standardize_train_eval(x: np.ndarray, train_mask: np.ndarray) -> np.ndarray:
    mean = x[train_mask].mean(axis=0)
    scale = x[train_mask].std(axis=0)
    scale[scale < 1e-8] = 1.0
    return ((x - mean) / scale).astype(np.float32)


def gap_only_features(x_phase1c: np.ndarray, emb_width: int) -> np.ndarray:
    # phase1c build_gap_features returns [emb, probe_prob, probe_logit,
    # probe_pred, signed_margin, min_abs_margin, train-only quality].
    # For fi-006 we remove raw emb so the capacity test is on legal gap-ledger
    # self-assessment signals, not a richer latent-state reader.
    return x_phase1c[:, emb_width:].astype(np.float64)


def prepare_data() -> PreparedData:
    data = load_npz_dict(NPZ_PATH)
    rows = flatten_transition_rows(data)
    splits = split_episodes(int(data["emb"].shape[0]))
    train_mask = np.isin(rows["episode"], splits["train"])
    cal_mask = np.isin(rows["episode"], splits["calibration"])
    eval_mask = np.isin(rows["episode"], splits["eval"])

    near_threshold = float(np.median(rows["distance_to_target"][train_mask]))
    y_dist = distinction_truth(rows, near_threshold, prefix="")
    probe_prob_cols: list[np.ndarray] = []
    probe_logit_cols: list[np.ndarray] = []
    probe_pred_cols: list[np.ndarray] = []
    for j, _name in enumerate(DISTINCTIONS):
        head, _info = fit_logistic_head(
            rows["emb"][train_mask],
            y_dist[train_mask, j],
            steps=700,
            lr=0.18,
            l2=1e-4,
        )
        p_all, logit_all = predict_logistic_head(head, rows["emb"])
        probe_prob_cols.append(p_all)
        probe_logit_cols.append(logit_all)
        probe_pred_cols.append((p_all >= 0.5).astype(np.float64))

    probe_prob = np.stack(probe_prob_cols, axis=1)
    probe_logit = np.stack(probe_logit_cols, axis=1)
    probe_pred = np.stack(probe_pred_cols, axis=1)
    quality_feature, _quality_report = fit_linear_r2_quality(
        rows["emb"][train_mask],
        rows["observation"][train_mask],
        rows["emb"][eval_mask],
        rows["observation"][eval_mask],
    )
    x_phase1c, _min_abs_margin = build_gap_features(
        rows["emb"],
        probe_prob,
        probe_logit,
        probe_pred,
        quality_feature,
        PRIMARY_PROBE_INDICES,
    )
    x = standardize_train_eval(gap_only_features(x_phase1c, rows["emb"].shape[1]), train_mask)

    tau_err = float(np.percentile(rows["mse"][train_mask], 75))
    y = (rows["mse"] > tau_err).astype(np.int8)
    _ = cal_mask  # Split intentionally preserved from phase1c; fi-006 trains on train and evaluates on eval.
    return PreparedData(
        x=x,
        y=y,
        episode=rows["episode"].astype(np.int64),
        train_mask=train_mask,
        eval_mask=eval_mask,
    )


def fit_reader(
    model: nn.Module,
    x_train: np.ndarray,
    y_train: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> nn.Module:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model.to(device)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_train.astype(np.float32)).to(device)
    pos = float(y_train.sum())
    neg = float(len(y_train) - y_train.sum())
    pos_weight = torch.tensor([neg / max(pos, 1.0)], dtype=torch.float32, device=device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    generator = torch.Generator(device="cpu").manual_seed(seed + 1009)

    model.train()
    for _epoch in range(EPOCHS):
        order = torch.randperm(len(y_train), generator=generator)
        for lo in range(0, len(y_train), BATCH_SIZE):
            idx = order[lo : lo + BATCH_SIZE].to(device)
            logits = model(x_t[idx])
            loss = nn.functional.binary_cross_entropy_with_logits(
                logits,
                y_t[idx],
                pos_weight=pos_weight,
            )
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite reader loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    return model


def predict_reader(model: nn.Module, x_eval: np.ndarray, device: torch.device) -> np.ndarray:
    out: list[np.ndarray] = []
    with torch.inference_mode():
        for lo in range(0, len(x_eval), BATCH_SIZE):
            hi = min(lo + BATCH_SIZE, len(x_eval))
            xb = torch.from_numpy(x_eval[lo:hi].astype(np.float32)).to(device)
            logits = model(xb).detach().cpu().numpy().astype(np.float64)
            out.append(logits)
    logits_all = np.concatenate(out, axis=0)
    return 1.0 / (1.0 + np.exp(-np.clip(logits_all, -60.0, 60.0)))


def train_and_score(
    reader_kind: str,
    x_train: np.ndarray,
    y_train: np.ndarray,
    x_eval: np.ndarray,
    *,
    seed: int,
    device: torch.device,
) -> np.ndarray:
    if reader_kind == "linear":
        model = LinearReader(x_train.shape[1])
    elif reader_kind == "mlp":
        model = MlpReader(x_train.shape[1])
    else:
        raise ValueError(reader_kind)
    fit_reader(model, x_train, y_train, seed=seed, device=device)
    score = predict_reader(model, x_eval, device)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return score


def paired_bootstrap_gain(
    y: np.ndarray,
    mlp_score: np.ndarray,
    linear_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
) -> dict[str, float]:
    mlp_auroc = clean_float(auroc_rank(y, mlp_score))
    linear_auroc = clean_float(auroc_rank(y, linear_score))
    observed = clean_float(mlp_auroc - linear_auroc)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    samples = np.empty(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in sampled])
        samples[i] = auroc_rank(y[idx], mlp_score[idx]) - auroc_rank(y[idx], linear_score[idx])
    return {
        "observed": observed,
        "low": clean_float(float(np.nanpercentile(samples, 2.5))),
        "high": clean_float(float(np.nanpercentile(samples, 97.5))),
        "mlp_auroc": mlp_auroc,
        "linear_auroc": linear_auroc,
    }


def reported_claim(metric: dict[str, float], verdict: str) -> str:
    return (
        f"MLP AUROC={metric['mlp_auroc']:.6f}, linear AUROC={metric['linear_auroc']:.6f}, "
        f"gain={metric['observed']:.6f}, 95% CI=[{metric['low']:.6f},{metric['high']:.6f}]; "
        f"delta_ci_above_zero={verdict}."
    )


def fail_closed_claim(reason: str) -> str:
    return (
        "MLP AUROC=0.500000, linear AUROC=0.500000, gain=0.000000, "
        f"95% CI=[0.000000,0.000000]; fail-closed: {reason}."
    )


def build_payload(seed: int) -> dict[str, Any]:
    set_determinism(seed)
    data = prepare_data()
    y_train = data.y[data.train_mask]
    y_eval = data.y[data.eval_mask]
    if np.unique(y_train).size < 2 or np.unique(y_eval).size < 2:
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
            "metric": METRIC,
            "metric_value": 0.0,
            "ci": {"low": 0.0, "high": 0.0},
            "status": "fail-closed",
            "measured_scope": [METRIC, "auroc"],
            "reported_claim": fail_closed_claim("train/eval prediction-error label is single-class"),
        }
        return clean_json(payload)

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    x_train = data.x[data.train_mask]
    x_eval = data.x[data.eval_mask]
    linear_score = train_and_score("linear", x_train, y_train, x_eval, seed=seed + 101, device=device)
    mlp_score = train_and_score("mlp", x_train, y_train, x_eval, seed=seed + 101, device=device)
    metric = paired_bootstrap_gain(
        y_eval,
        mlp_score,
        linear_score,
        data.episode[data.eval_mask],
        seed=seed + BOOTSTRAP_SEED_OFFSET,
    )

    if metric["low"] > 0.0:
        verdict = "positive"
    elif metric["high"] <= 0.0:
        verdict = "negative"
    else:
        verdict = "unidentifiable"

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": metric["observed"],
        "ci": {"low": metric["low"], "high": metric["high"]},
        "measured_scope": [METRIC, "auroc"],
        "reported_claim": reported_claim(metric, verdict),
    }
    if verdict == "unidentifiable":
        payload["status"] = "fail-closed"
    return clean_json(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, help="Path to write the frozen verdict payload JSON.")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = build_payload(args.seed)
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
