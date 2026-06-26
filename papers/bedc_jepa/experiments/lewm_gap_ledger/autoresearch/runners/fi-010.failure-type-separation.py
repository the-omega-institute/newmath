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
CACHE_DIR = ROOT / "reports" / "phase2c_materialized_cache"

HYPOTHESIS_ID = "fi-010.failure-type-separation"
METRIC = "failure_type_macro_auroc"
FAMILIES = ("background_tint", "color_shift", "occlusion", "brightness", "gaussian_noise")
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
BATCH_SIZE = 65536
EPOCHS = 800
LR = 2.0e-3
WEIGHT_DECAY = 1.0e-4

FEATURE_AUDIT = [
    (
        "agent_room_right_probe_probability",
        "current perturbed latent is passed through the phase1c train-split probe; this is a ledger self-assessment signal and not the perturbation family label.",
    ),
    (
        "agent_room_right_probe_logit",
        "the same probe's confidence logit; it contains no family name, strength token, row id, episode id, RGB perturbation parameter, or failure-type target.",
    ),
    (
        "agent_room_right_probe_prediction",
        "the thresholded probe output; it is a current-anchor self-description and is not fitted on eval family labels.",
    ),
    (
        "agent_room_right_signed_margin",
        "phase1c signed margin derived from the probe logit; it is a confidence/margin channel, not a type-defining perturbation variable.",
    ),
    (
        "agent_room_right_min_abs_margin",
        "absolute probe margin for the single primary probe; it is an uncertainty channel and does not encode family or strength directly.",
    ),
    (
        "emb_to_observation_train_r2_quality_vector",
        "train-split-only constant quality features from phase1c; they do not vary by eval sample and cannot identify the perturbation family.",
    ),
]


@dataclass(frozen=True)
class PreparedData:
    x_train: np.ndarray
    y_train: np.ndarray
    x_eval: np.ndarray
    y_eval: np.ndarray
    group_eval: np.ndarray
    class_counts_train: list[int]
    class_counts_eval: list[int]
    device_name: str


class OvrReader(nn.Module):
    def __init__(self, in_dim: int, n_classes: int) -> None:
        super().__init__()
        self.linear = nn.Linear(in_dim, n_classes)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.linear(x)


def set_determinism(seed: int) -> torch.device:
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


def macro_auroc(y_class: np.ndarray, scores: np.ndarray, n_classes: int) -> float:
    if len(y_class) == 0 or np.unique(y_class).size < 2:
        return 0.5
    values = []
    for class_id in range(n_classes):
        binary = (y_class == class_id).astype(np.int8)
        values.append(auroc_rank(binary, scores[:, class_id]))
    return clean_float(float(np.mean(values)))


def load_emb_width() -> int:
    with np.load(NPZ_PATH, allow_pickle=False) as raw:
        return int(raw["emb"].shape[-1])


def cache_paths(split_name: str, family: str) -> list[Path]:
    return sorted(CACHE_DIR.glob(f"{split_name}_{family}_*.npz"), key=lambda p: p.name)


def load_family_split(split_name: str, family: str, class_id: int, emb_width: int) -> dict[str, np.ndarray]:
    x_parts: list[np.ndarray] = []
    y_parts: list[np.ndarray] = []
    group_parts: list[np.ndarray] = []
    paths = cache_paths(split_name, family)
    if not paths:
        raise FileNotFoundError(f"missing phase2c cache for split={split_name}, family={family}")

    for path in paths:
        with np.load(path, allow_pickle=False) as raw:
            y_failure = raw["y"].astype(np.int8)
            keep = y_failure > 0
            if not np.any(keep):
                continue
            x = raw["x"].astype(np.float64)
            if x.shape[1] <= emb_width:
                raise ValueError(f"cache feature width {x.shape[1]} does not exceed emb width {emb_width}: {path}")

            # phase2c x is phase1c build_gap_features:
            # [raw emb, probe prob, probe logit, probe pred, signed margin,
            # min_abs_margin, train-only quality].  The raw embedding is a
            # richer state reader and could encode visual family identity, so
            # fi-010 drops it and keeps only gap-ledger self-assessment columns.
            x_gap = x[:, emb_width:].astype(np.float64)
            episode = raw["episode"].astype(np.int64)
            x_parts.append(x_gap[keep])
            y_parts.append(np.full(int(keep.sum()), class_id, dtype=np.int64))
            group_parts.append((class_id * 1_000_000 + episode[keep]).astype(np.int64))

    if not x_parts:
        return {
            "x": np.zeros((0, 0), dtype=np.float64),
            "y": np.zeros(0, dtype=np.int64),
            "group": np.zeros(0, dtype=np.int64),
        }
    return {
        "x": np.concatenate(x_parts, axis=0).astype(np.float64),
        "y": np.concatenate(y_parts, axis=0).astype(np.int64),
        "group": np.concatenate(group_parts, axis=0).astype(np.int64),
    }


def standardize_by_train(x_train: np.ndarray, x_eval: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = x_train.mean(axis=0)
    scale = x_train.std(axis=0)
    scale[scale < 1.0e-8] = 1.0
    return ((x_train - mean) / scale).astype(np.float32), ((x_eval - mean) / scale).astype(np.float32)


def prepare_data(device: torch.device) -> PreparedData:
    emb_width = load_emb_width()
    train_parts = [load_family_split("train", family, i, emb_width) for i, family in enumerate(FAMILIES)]
    eval_parts = [load_family_split("eval", family, i, emb_width) for i, family in enumerate(FAMILIES)]

    train_nonempty = [p for p in train_parts if p["x"].size]
    eval_nonempty = [p for p in eval_parts if p["x"].size]
    if not train_nonempty or not eval_nonempty:
        return PreparedData(
            x_train=np.zeros((0, 0), dtype=np.float32),
            y_train=np.zeros(0, dtype=np.int64),
            x_eval=np.zeros((0, 0), dtype=np.float32),
            y_eval=np.zeros(0, dtype=np.int64),
            group_eval=np.zeros(0, dtype=np.int64),
            class_counts_train=[0 for _ in FAMILIES],
            class_counts_eval=[0 for _ in FAMILIES],
            device_name=str(device),
        )

    x_train_raw = np.concatenate([p["x"] for p in train_nonempty], axis=0)
    y_train = np.concatenate([p["y"] for p in train_nonempty], axis=0).astype(np.int64)
    x_eval_raw = np.concatenate([p["x"] for p in eval_nonempty], axis=0)
    y_eval = np.concatenate([p["y"] for p in eval_nonempty], axis=0).astype(np.int64)
    group_eval = np.concatenate([p["group"] for p in eval_nonempty], axis=0).astype(np.int64)
    x_train, x_eval = standardize_by_train(x_train_raw, x_eval_raw)
    return PreparedData(
        x_train=x_train,
        y_train=y_train,
        x_eval=x_eval,
        y_eval=y_eval,
        group_eval=group_eval,
        class_counts_train=[int(np.sum(y_train == i)) for i in range(len(FAMILIES))],
        class_counts_eval=[int(np.sum(y_eval == i)) for i in range(len(FAMILIES))],
        device_name=str(device),
    )


def fit_reader(data: PreparedData, *, seed: int, device: torch.device) -> OvrReader:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = OvrReader(data.x_train.shape[1], len(FAMILIES)).to(device)
    x_t = torch.from_numpy(data.x_train).to(device)
    y_onehot = np.zeros((len(data.y_train), len(FAMILIES)), dtype=np.float32)
    y_onehot[np.arange(len(data.y_train)), data.y_train] = 1.0
    y_t = torch.from_numpy(y_onehot).to(device)
    pos = y_onehot.sum(axis=0)
    neg = len(y_onehot) - pos
    pos_weight = torch.from_numpy((neg / np.maximum(pos, 1.0)).astype(np.float32)).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    generator = torch.Generator(device="cpu").manual_seed(seed + 1009)

    model.train()
    for _epoch in range(EPOCHS):
        order = torch.randperm(len(data.y_train), generator=generator)
        for lo in range(0, len(order), BATCH_SIZE):
            idx = order[lo : lo + BATCH_SIZE].to(device)
            logits = model(x_t[idx])
            loss = nn.functional.binary_cross_entropy_with_logits(logits, y_t[idx], pos_weight=pos_weight)
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite OVR reader loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    return model.eval()


def predict_scores(model: OvrReader, x: np.ndarray, device: torch.device) -> np.ndarray:
    chunks: list[np.ndarray] = []
    with torch.inference_mode():
        for lo in range(0, len(x), BATCH_SIZE):
            hi = min(lo + BATCH_SIZE, len(x))
            xb = torch.from_numpy(x[lo:hi]).to(device)
            chunks.append(model(xb).detach().cpu().numpy().astype(np.float64))
    return np.concatenate(chunks, axis=0)


def bootstrap_macro_auroc(y: np.ndarray, scores: np.ndarray, groups: np.ndarray, *, seed: int) -> dict[str, Any]:
    observed = macro_auroc(y, scores, len(FAMILIES))
    unique_groups = np.unique(groups)
    by_group = [np.where(groups == group)[0] for group in unique_groups]
    rng = np.random.default_rng(seed)
    samples = np.empty(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        chosen = rng.integers(0, len(by_group), size=len(by_group))
        idx = np.concatenate([by_group[j] for j in chosen])
        samples[i] = macro_auroc(y[idx], scores[idx], len(FAMILIES))
    class_aurocs = [
        clean_float(auroc_rank((y == i).astype(np.int8), scores[:, i]))
        for i in range(len(FAMILIES))
    ]
    return {
        "observed": clean_float(observed),
        "low": clean_float(float(np.nanpercentile(samples, 2.5))),
        "high": clean_float(float(np.nanpercentile(samples, 97.5))),
        "class_aurocs": class_aurocs,
    }


def fail_closed_payload(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.5,
        "ci": {"low": 0.5, "high": 0.5},
        "status": "fail-closed",
        "measured_scope": [METRIC, "auroc"],
        "reported_claim": (
            "fail-closed: failure-type macro AUROC is unidentifiable; "
            f"{reason}."
        ),
    }


def measured_claim(metric: dict[str, Any], data: PreparedData, verdict: str) -> str:
    class_pairs = ", ".join(
        f"{family}={metric['class_aurocs'][i]:.6f}" for i, family in enumerate(FAMILIES)
    )
    return (
        f"phase2c failure-only perturbation-family reader: classes={len(FAMILIES)}, "
        f"train_counts={data.class_counts_train}, eval_counts={data.class_counts_eval}, "
        f"macro AUROC={metric['observed']:.6f}, 95% CI=[{metric['low']:.6f},{metric['high']:.6f}], "
        f"one-vs-rest AUROCs: {class_pairs}; criterion auroc_ci_separation vs 0.5 is {verdict}. "
        "Scope is cached tworooms phase2c perturbation families only."
    )


def build_payload(seed: int) -> dict[str, Any]:
    device = set_determinism(seed)
    data = prepare_data(device)
    if len(data.y_train) == 0 or len(data.y_eval) == 0:
        return clean_json(fail_closed_payload("no train/eval failure rows were available in the phase2c family cache"))
    if np.unique(data.y_train).size < 2 or np.unique(data.y_eval).size < 2:
        return clean_json(fail_closed_payload("train or eval failure-type labels are single-class"))
    if any(count == 0 for count in data.class_counts_train) or any(count == 0 for count in data.class_counts_eval):
        return clean_json(fail_closed_payload("at least one perturbation family has zero failure rows in train or eval"))

    model = fit_reader(data, seed=seed + 11, device=device)
    scores = predict_scores(model, data.x_eval, device)
    metric = bootstrap_macro_auroc(
        data.y_eval,
        scores,
        data.group_eval,
        seed=seed + BOOTSTRAP_SEED_OFFSET,
    )
    if not all(math.isfinite(float(metric[k])) for k in ("observed", "low", "high")):
        return clean_json(fail_closed_payload("macro AUROC bootstrap produced a non-finite value"))

    verdict = "positive" if metric["low"] > 0.5 else "negative_or_inconclusive"
    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": metric["observed"],
        "ci": {"low": metric["low"], "high": metric["high"]},
        "measured_scope": [METRIC, "auroc"],
        "reported_claim": measured_claim(metric, data, verdict),
    }
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
