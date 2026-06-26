#!/usr/bin/env python3
from __future__ import annotations

import argparse
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
sys.path.insert(0, str(ROOT))

from _phase1c_gap_ledger import (  # noqa: E402
    DISTINCTIONS,
    FEATURE_VARIANTS,
    auroc_rank,
    build_gap_features,
    distinction_truth,
    fit_linear_r2_quality,
    fit_logistic_head,
    flatten_transition_rows,
    predict_logistic_head,
    split_episodes,
)


HYPOTHESIS_ID = "fi-016.detection-vs-strongest-posthoc"
METRIC = "native_minus_strongest_posthoc_auroc"
LATENT_NPZ = ROOT / "tworooms_latent_large.npz"
CLEAN_LABELS = ROOT / "reports" / "g2n_labels_clean.npz"

SPLIT_SEED = 1701
BOOTSTRAP_SEED_OFFSET = 314159
BOOTSTRAPS = 500
PRIMARY_H = 1
PRIMARY_Q = 75

HORIZONS = (1, 3, 5, 10)
QUANTILES = (50, 75, 90)
H_TO_LABEL_IDX = {1: 0, 3: 2, 5: 4, 10: 9}
Q_TO_IDX = {50: 0, 75: 1, 90: 2}

WINDOW = 6
MAX_FUTURE_TOKENS = 5
D_MODEL = 64
N_HEADS = 4
N_LAYERS = 2
FFN_DIM = 128
EPOCHS = 30
BATCH = 256
LR = 1.0e-3

EXPECTED_PHASE1C_CAMPAIGN_AUROC = 0.7313653225855256
PHASE1C_ANCHOR_TOL = 1.0e-9


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
        raise ValueError(f"non-finite JSON float: {out!r}")
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


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as raw:
        return {k: raw[k] for k in raw.files}


def sigmoid_np(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


def output_col(h: int, q: int) -> int:
    return HORIZONS.index(h) * len(QUANTILES) + Q_TO_IDX[q]


def pair_to_row_index(rows: dict[str, np.ndarray]) -> dict[tuple[int, int], int]:
    return {(int(ep), int(t)): i for i, (ep, t) in enumerate(zip(rows["episode"], rows["t"]))}


def valid_transition_count(data: dict[str, np.ndarray], ep: int) -> int:
    return int(data["transition_mask"][ep].astype(bool).sum())


def fit_phase1c_campaign_scores(
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
) -> dict[str, Any]:
    splits_ep = split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701:
        raise RuntimeError("split seed sanity failed")
    split_masks = {name: np.isin(rows["episode"], eps) for name, eps in splits_ep.items()}
    train_mask = split_masks["train"]
    eval_mask = split_masks["eval"]

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
            l2=1.0e-4,
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
    x_b, _ = build_gap_features(
        rows["emb"],
        probe_prob,
        probe_logit,
        probe_pred,
        quality_feature,
        FEATURE_VARIANTS["B_denoised_agent_room_only"],
    )

    tau_err = float(np.percentile(rows["mse"][train_mask], 75))
    y_prediction_error = (rows["mse"] > tau_err).astype(np.int8)
    head, fit_info = fit_logistic_head(
        x_b[train_mask],
        y_prediction_error[train_mask],
        steps=500,
        lr=0.14,
        l2=1.0e-4,
    )
    score_all, _ = predict_logistic_head(head, x_b)
    campaign_eval_auroc = float(auroc_rank(y_prediction_error[eval_mask], score_all[eval_mask]))
    return {
        "score_all": score_all.astype(np.float64),
        "y_all": y_prediction_error,
        "episode_all": rows["episode"].astype(np.int64),
        "fit": fit_info,
        "tau_err": tau_err,
        "campaign_eval_auroc": campaign_eval_auroc,
    }


def build_clean_examples(
    data: dict[str, np.ndarray],
    labels: dict[str, np.ndarray],
    split: str,
) -> dict[str, np.ndarray]:
    anchors = labels[f"{split}_anchor_ep_t0"].astype(np.int64)
    emb_np = data["emb"].astype(np.float32)
    act_np = data["action"].astype(np.float32)
    emb_dim = emb_np.shape[-1]
    act_dim = act_np.shape[-1]
    n = len(anchors)

    past_z = np.zeros((n, WINDOW, emb_dim), dtype=np.float32)
    past_a = np.zeros((n, WINDOW, act_dim), dtype=np.float32)
    future_z = np.zeros((n, MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
    future_delta = np.zeros((n, MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
    future_avail = labels[f"{split}_valid"][:, :MAX_FUTURE_TOKENS].astype(bool)
    pred_z = labels[f"{split}_pred_z"][:, :MAX_FUTURE_TOKENS].astype(np.float32)
    t_scalar = np.zeros(n, dtype=np.float32)
    y = np.zeros((n, len(HORIZONS), len(QUANTILES)), dtype=np.float32)
    valid = np.zeros_like(y, dtype=bool)
    clean_y = labels[f"{split}_y"].astype(np.int8)
    clean_valid = labels[f"{split}_valid"].astype(bool)

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

    return {
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
    }


def compute_norm(ex: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    z = ex["past_z"].reshape(-1, ex["past_z"].shape[-1])
    mean = z.mean(axis=0).astype(np.float32)
    std = (z.std(axis=0) + 1.0e-6).astype(np.float32)
    fut = ex["future_delta"][ex["future_avail"].astype(bool)]
    if len(fut):
        d_mean = fut.mean(axis=0).astype(np.float32)
        d_std = (fut.std(axis=0) + 1.0e-6).astype(np.float32)
    else:
        d_mean = np.zeros_like(mean)
        d_std = np.ones_like(std)
    return {"z_mean": mean, "z_std": std, "delta_mean": d_mean, "delta_std": d_std}


def normalize_examples(ex: dict[str, np.ndarray], norm: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    out = dict(ex)
    out["past_z"] = ((ex["past_z"] - norm["z_mean"]) / norm["z_std"]).astype(np.float32)
    out["future_z"] = ((ex["future_z"] - norm["z_mean"]) / norm["z_std"]).astype(np.float32)
    out["future_delta"] = ((ex["future_delta"] - norm["delta_mean"]) / norm["delta_std"]).astype(np.float32)
    return out


class NativeLedgerTransformer(nn.Module):
    def __init__(self, emb_dim: int, act_dim: int) -> None:
        super().__init__()
        token_dim = emb_dim * 2 + act_dim + 1
        self.emb_dim = emb_dim
        self.act_dim = act_dim
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
        t_future = t_scalar[:, None, None].expand(b, MAX_FUTURE_TOKENS, 1)
        future = torch.cat(
            [
                future_z,
                future_delta,
                torch.zeros(b, MAX_FUTURE_TOKENS, self.act_dim, device=past_z.device, dtype=past_z.dtype),
                t_future,
            ],
            dim=-1,
        )
        query = torch.zeros(b, 1, self.emb_dim * 2 + self.act_dim + 1, device=past_z.device, dtype=past_z.dtype)
        x = torch.cat([past, future, query], dim=1)
        type_ids = torch.cat(
            [
                torch.zeros(b, WINDOW, device=past_z.device, dtype=torch.long),
                torch.ones(b, MAX_FUTURE_TOKENS, device=past_z.device, dtype=torch.long),
                torch.full((b, 1), 2, device=past_z.device, dtype=torch.long),
            ],
            dim=1,
        )
        key_padding = torch.cat(
            [
                torch.zeros(b, WINDOW, device=past_z.device, dtype=torch.bool),
                ~future_avail.bool(),
                torch.zeros(b, 1, device=past_z.device, dtype=torch.bool),
            ],
            dim=1,
        )
        h = self.token_proj(x) + self.type_emb(type_ids) + self.pos[: x.shape[1]].unsqueeze(0)
        h = self.encoder(h, src_key_padding_mask=key_padding)
        return self.head(h[:, -1])


def train_native_clean_horizon(
    train_ex: dict[str, np.ndarray],
    *,
    seed: int,
    device: torch.device,
) -> tuple[NativeLedgerTransformer, dict[str, np.ndarray]]:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    norm = compute_norm(train_ex)
    exn = normalize_examples(train_ex, norm)
    model = NativeLedgerTransformer(exn["past_z"].shape[-1], exn["past_a"].shape[-1]).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=LR)
    tensors = {
        "past_z": torch.from_numpy(exn["past_z"].astype(np.float32)).to(device),
        "past_a": torch.from_numpy(exn["past_a"].astype(np.float32)).to(device),
        "future_z": torch.from_numpy(exn["future_z"].astype(np.float32)).to(device),
        "future_delta": torch.from_numpy(exn["future_delta"].astype(np.float32)).to(device),
        "future_avail": torch.from_numpy(exn["future_avail"].astype(bool)).to(device),
        "t_scalar": torch.from_numpy(exn["t_scalar"].astype(np.float32)).to(device),
        "y": torch.from_numpy(exn["y"].reshape(len(exn["y"]), -1).astype(np.float32)).to(device),
        "valid": torch.from_numpy(exn["valid"].reshape(len(exn["valid"]), -1).astype(bool)).to(device),
    }
    generator = torch.Generator(device="cpu").manual_seed(seed + 1009)
    n = len(exn["episode"])
    model.train()
    for _epoch in range(EPOCHS):
        order = torch.randperm(n, generator=generator)
        for lo in range(0, n, BATCH):
            idx = order[lo : lo + BATCH].to(device)
            logits = model(
                tensors["past_z"][idx],
                tensors["past_a"][idx],
                tensors["future_z"][idx],
                tensors["future_delta"][idx],
                tensors["future_avail"][idx],
                tensors["t_scalar"][idx],
            )
            per = F.binary_cross_entropy_with_logits(logits, tensors["y"][idx], reduction="none")
            mask = tensors["valid"][idx].float()
            loss = (per * mask).sum() / mask.sum().clamp_min(1.0)
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite native horizon loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            opt.step()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model, norm


def predict_native_logits(
    model: NativeLedgerTransformer,
    ex: dict[str, np.ndarray],
    norm: dict[str, np.ndarray],
    device: torch.device,
) -> np.ndarray:
    exn = normalize_examples(ex, norm)
    out = np.zeros((len(exn["episode"]), len(HORIZONS) * len(QUANTILES)), dtype=np.float64)
    with torch.inference_mode():
        for lo in range(0, len(out), 512):
            hi = min(lo + 512, len(out))
            logits = model(
                torch.from_numpy(exn["past_z"][lo:hi].astype(np.float32)).to(device),
                torch.from_numpy(exn["past_a"][lo:hi].astype(np.float32)).to(device),
                torch.from_numpy(exn["future_z"][lo:hi].astype(np.float32)).to(device),
                torch.from_numpy(exn["future_delta"][lo:hi].astype(np.float32)).to(device),
                torch.from_numpy(exn["future_avail"][lo:hi].astype(bool)).to(device),
                torch.from_numpy(exn["t_scalar"][lo:hi].astype(np.float32)).to(device),
            )
            out[lo:hi] = logits.detach().cpu().numpy().astype(np.float64)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return out


def metric_stat(observed: float, samples: np.ndarray) -> dict[str, float]:
    arr = np.asarray(samples, dtype=np.float64)
    if not np.isfinite(arr).all():
        raise RuntimeError("non-finite bootstrap sample")
    return {
        "observed": float(observed),
        "low": float(np.percentile(arr, 2.5)),
        "high": float(np.percentile(arr, 97.5)),
    }


def paired_episode_bootstrap(
    y: np.ndarray,
    native_score: np.ndarray,
    posthoc_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
) -> dict[str, Any]:
    y = y.astype(np.int8)
    native_score = native_score.astype(np.float64)
    posthoc_score = posthoc_score.astype(np.float64)
    episode = episode.astype(np.int64)
    if not (len(y) == len(native_score) == len(posthoc_score) == len(episode)):
        raise RuntimeError("paired arrays have inconsistent lengths")
    if np.unique(y).size < 2:
        raise RuntimeError("eval_h1 truth is single-class")

    native_obs = float(auroc_rank(y, native_score))
    posthoc_obs = float(auroc_rank(y, posthoc_score))
    delta_obs = native_obs - posthoc_obs

    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    delta_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    native_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    posthoc_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        picked = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in picked])
        if np.unique(y[idx]).size < 2:
            raise RuntimeError("single-class paired bootstrap resample")
        n_auc = float(auroc_rank(y[idx], native_score[idx]))
        p_auc = float(auroc_rank(y[idx], posthoc_score[idx]))
        native_samples[i] = n_auc
        posthoc_samples[i] = p_auc
        delta_samples[i] = n_auc - p_auc

    return {
        "delta": metric_stat(delta_obs, delta_samples),
        "native": metric_stat(native_obs, native_samples),
        "posthoc": metric_stat(posthoc_obs, posthoc_samples),
        "eval_rows": int(len(y)),
        "eval_episodes": int(len(unique_ep)),
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
    }


def make_payload(
    metric_value: float,
    ci_low: float,
    ci_high: float,
    claim: str,
    *,
    fail_closed: bool,
) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": float(metric_value),
        "ci": {"low": float(ci_low), "high": float(ci_high)},
        "measured_scope": ["native_minus_strongest_posthoc_auroc", "auroc"],
        "reported_claim": claim,
    }
    if fail_closed:
        payload["status"] = "fail-closed"
    return payload


def fail_payload(reason: str) -> dict[str, Any]:
    return make_payload(
        0.0,
        0.0,
        0.0,
        f"fail-closed: {reason}; native did not establish superiority over the strongest logistic post-hoc probe.",
        fail_closed=True,
    )


def build_payload(seed: int) -> dict[str, Any]:
    device = configure_determinism(seed)
    if not LATENT_NPZ.exists() or not CLEAN_LABELS.exists():
        return fail_payload("missing tworooms latent or clean horizon labels input")

    data = load_npz(LATENT_NPZ)
    labels = load_npz(CLEAN_LABELS)
    rows = flatten_transition_rows(data)
    pair_row = pair_to_row_index(rows)

    posthoc = fit_phase1c_campaign_scores(data, rows)
    campaign_anchor_delta = abs(float(posthoc["campaign_eval_auroc"]) - EXPECTED_PHASE1C_CAMPAIGN_AUROC)
    if campaign_anchor_delta > PHASE1C_ANCHOR_TOL:
        return fail_payload(
            "Phase1c campaign logistic gap head anchor mismatch: "
            f"observed={float(posthoc['campaign_eval_auroc']):.17g}, "
            f"expected={EXPECTED_PHASE1C_CAMPAIGN_AUROC:.17g}"
        )

    train_ex = build_clean_examples(data, labels, "train")
    eval_ex = build_clean_examples(data, labels, "eval")
    model, norm = train_native_clean_horizon(train_ex, seed=seed + 11, device=device)
    eval_logits = predict_native_logits(model, eval_ex, norm, device)

    h_idx = H_TO_LABEL_IDX[PRIMARY_H]
    q_idx = Q_TO_IDX[PRIMARY_Q]
    valid = labels["eval_valid"][:, h_idx].astype(bool)
    y = labels["eval_y"][valid, h_idx, q_idx].astype(np.int8)
    episode = eval_ex["episode"][valid].astype(np.int64)
    native_score = eval_logits[valid, output_col(PRIMARY_H, PRIMARY_Q)].astype(np.float64)

    row_idx = np.asarray(
        [pair_row[(int(ep), int(t))] for ep, t in eval_ex["anchor_ep_t0"][valid]],
        dtype=np.int64,
    )
    posthoc_score = posthoc["score_all"][row_idx].astype(np.float64)
    posthoc_y = posthoc["y_all"][row_idx].astype(np.int8)
    if not np.array_equal(y, posthoc_y):
        return fail_payload("eval_h1 anchor alignment failed between native labels and Phase1c rows")
    if np.unique(y).size < 2:
        return fail_payload("eval_h1 truth is single-class")

    paired = paired_episode_bootstrap(
        y,
        native_score,
        posthoc_score,
        episode,
        seed=seed + BOOTSTRAP_SEED_OFFSET,
    )
    delta = paired["delta"]
    native = paired["native"]
    strongest = paired["posthoc"]

    if float(delta["low"]) > 0.0:
        conclusion = "positive: CI low>0, native still exceeds the strongest logistic post-hoc probe"
        fail_closed = False
    elif float(delta["high"]) < 0.0:
        conclusion = "negative: CI high<0, native does not exceed the strongest logistic post-hoc probe"
        fail_closed = False
    else:
        conclusion = "unidentifiable: CI crosses 0, native superiority over the strongest logistic post-hoc probe is not established"
        fail_closed = True

    claim = (
        f"native_auroc={native['observed']:.9g}; "
        f"strongest_posthoc_auroc={strongest['observed']:.9g} "
        f"(Phase1c logistic gap head, campaign eval anchor={float(posthoc['campaign_eval_auroc']):.9g}); "
        f"gap={delta['observed']:.9g}, 95% CI=[{delta['low']:.9g},{delta['high']:.9g}]; "
        f"paired eval_h1 rows={paired['eval_rows']}, episodes={paired['eval_episodes']}; "
        f"{conclusion}."
    )
    return make_payload(
        float(delta["observed"]),
        float(delta["low"]),
        float(delta["high"]),
        claim,
        fail_closed=fail_closed,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = clean_json(build_payload(int(args.seed)))
    forbidden = ("real_robot_transfer", "paper_claim_strength")
    claim = str(payload.get("reported_claim", ""))
    if any(token in claim for token in forbidden):
        raise RuntimeError("reported_claim contains a forbidden scope token")
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
