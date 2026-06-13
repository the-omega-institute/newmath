#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
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
import torch.nn.functional as F


ROOT = Path(__file__).resolve().parents[2]
BASE_RUNNER = Path(__file__).resolve().with_name("fi-014.fromscratch-encoder-allocation.py")

HYPOTHESIS_ID = "fi-017.g2n-integrated-detection-allocation"
METRIC = "allocation_delta"

EPOCHS = 96
BATCH = 96
LR = 5.0e-4
WEIGHT_DECAY = 5.0e-5
PRED_WEIGHT = 0.12
VAR_WEIGHT = 25.0
COV_WEIGHT = 4.0
TAIL_RANK_WEIGHT = 1.10
TAIL_REG_WEIGHT = 0.25
CVAR_WEIGHT = 5.0
DET_BCE_WEIGHT = 1.0

HEALTH_VAR_MEAN_MIN = 0.25
HEALTH_VAR_MIN_MIN = 1.0e-3
HEALTH_EFFECTIVE_RANK_MIN = 18.0

BOOTSTRAP_SEED_OFFSET = 314159
EPS = 1.0e-8

FIXED_LEWM_CEILING_TEXT = "fixed-LeWM ceiling: fi-012 about +0.005, fi-013 about +0.008"

FORBIDDEN_CLAIM_TOKENS = (
    "real" + "_robot" + "_transfer",
    "paper" + "_claim" + "_strength",
    "full" + "-lejepa",
    "global" + "-quality",
    "full" + "-tensor" + "-namecert",
    "llm" + "-behavior",
)


def load_base() -> Any:
    spec = importlib.util.spec_from_file_location("_fi014_base", BASE_RUNNER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


base = load_base()

base.HYPOTHESIS_ID = HYPOTHESIS_ID
base.METRIC = METRIC
base.EPOCHS = EPOCHS
base.BATCH = BATCH
base.LR = LR
base.WEIGHT_DECAY = WEIGHT_DECAY
base.PRED_WEIGHT = PRED_WEIGHT
base.VAR_WEIGHT = VAR_WEIGHT
base.COV_WEIGHT = COV_WEIGHT
base.TAIL_RANK_WEIGHT = TAIL_RANK_WEIGHT
base.TAIL_REG_WEIGHT = TAIL_REG_WEIGHT
base.CVAR_WEIGHT = CVAR_WEIGHT
base.FIXED_LEWM_CEILING_TEXT = FIXED_LEWM_CEILING_TEXT


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


def variance_loss(z: torch.Tensor) -> torch.Tensor:
    if z.shape[0] < 2:
        return z.sum() * 0.0
    std = torch.sqrt(z.var(dim=0, unbiased=False) + EPS)
    return torch.mean(F.relu(1.0 - std).pow(2))


def covariance_loss(z: torch.Tensor) -> torch.Tensor:
    n, d = z.shape
    if n < 2 or d < 2:
        return z.sum() * 0.0
    centered = z - z.mean(dim=0)
    cov = centered.T @ centered / float(n - 1)
    std = torch.sqrt(torch.diag(cov).clamp_min(EPS))
    corr = cov / (std[:, None] * std[None, :]).clamp_min(EPS)
    off = corr - torch.diag(torch.diag(corr))
    return off.pow(2).sum() / float(d)


def init_native_model(model: torch.nn.Module) -> None:
    for module in model.modules():
        if isinstance(module, (torch.nn.Conv2d, torch.nn.Linear)):
            torch.nn.init.kaiming_uniform_(module.weight, a=math.sqrt(5.0))
            if module.bias is not None:
                fan_in, _ = torch.nn.init._calculate_fan_in_and_fan_out(module.weight)
                bound = 1.0 / math.sqrt(fan_in) if fan_in > 0 else 0.0
                torch.nn.init.uniform_(module.bias, -bound, bound)


class G2NIntegratedModel(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        native = base.NativeEncoderModel()
        self.encoder = native.encoder
        self.action_encoder = native.action_encoder
        self.predictor = native.predictor
        self.tail_head = native.tail_head
        self.det_head = nn.Sequential(
            nn.LayerNorm(base.LATENT_DIM),
            nn.Linear(base.LATENT_DIM, 64),
            nn.GELU(),
            nn.Linear(64, 1),
        )

    def encode(self, x: torch.Tensor) -> torch.Tensor:
        return self.encoder(x)

    def forward(
        self, x: torch.Tensor, action: torch.Tensor
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        z = self.encoder(x)
        a = self.action_encoder(action)
        pred = self.predictor(torch.cat([z, a], dim=1))
        score = self.tail_head(z).squeeze(-1)
        det_logit = self.det_head(z).squeeze(-1)
        return z, pred, score, det_logit


class DetectionPixelRows(
    torch.utils.data.Dataset[
        tuple[
            torch.Tensor,
            torch.Tensor,
            torch.Tensor,
            torch.Tensor,
            torch.Tensor,
            torch.Tensor,
            torch.Tensor,
            torch.Tensor,
        ]
    ]
):
    def __init__(
        self,
        *,
        current_pixels: np.ndarray,
        next_pixels: np.ndarray,
        actions: np.ndarray,
        y_mean: np.ndarray,
        y_log: np.ndarray,
        episode: np.ndarray,
        tail_weight: np.ndarray,
        y_det: np.ndarray,
    ) -> None:
        self.current_pixels = current_pixels.astype(np.float32, copy=False)
        self.next_pixels = next_pixels.astype(np.float32, copy=False)
        self.actions = actions.astype(np.float32, copy=False)
        self.y_mean = y_mean.astype(np.float32)
        self.y_log = y_log.astype(np.float32)
        self.episode = episode.astype(np.int64)
        self.tail_weight = tail_weight.astype(np.float32)
        self.y_det = y_det.astype(np.float32)

    def __len__(self) -> int:
        return int(len(self.current_pixels))

    def __getitem__(
        self, index: int
    ) -> tuple[
        torch.Tensor,
        torch.Tensor,
        torch.Tensor,
        torch.Tensor,
        torch.Tensor,
        torch.Tensor,
        torch.Tensor,
        torch.Tensor,
    ]:
        cur = torch.from_numpy(self.current_pixels[index])
        nxt = torch.from_numpy(self.next_pixels[index])
        action = torch.from_numpy(self.actions[index])
        y = torch.tensor(float(self.y_mean[index]), dtype=torch.float32)
        ylog = torch.tensor(float(self.y_log[index]), dtype=torch.float32)
        ep = torch.tensor(int(self.episode[index]), dtype=torch.int64)
        tw = torch.tensor(float(self.tail_weight[index]), dtype=torch.float32)
        y_det = torch.tensor(float(self.y_det[index]), dtype=torch.float32)
        return cur, nxt, action, y, ylog, ep, tw, y_det


def train_native_encoder(
    dataset: Any,
    *,
    seed: int,
    device: torch.device,
) -> torch.nn.Module:
    torch.manual_seed(seed)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed)
    model = G2NIntegratedModel().to(device)
    init_native_model(model)
    opt = torch.optim.AdamW(model.parameters(), lr=LR, weight_decay=WEIGHT_DECAY)
    generator = torch.Generator(device="cpu").manual_seed(seed + 4703)
    loader = torch.utils.data.DataLoader(
        dataset,
        batch_size=BATCH,
        shuffle=True,
        generator=generator,
        num_workers=0,
        drop_last=True,
        pin_memory=(device.type == "cuda"),
    )
    model.train()
    for epoch in range(EPOCHS):
        for cur, nxt, action, y, ylog, ep, tw, y_det in loader:
            cur = cur.to(device, non_blocking=False)
            nxt = nxt.to(device, non_blocking=False)
            action = action.to(device, non_blocking=False)
            y = y.to(device, non_blocking=False)
            ylog = ylog.to(device, non_blocking=False)
            ep = ep.to(device, non_blocking=False)
            tw = tw.to(device, non_blocking=False)
            y_det = y_det.to(device, non_blocking=False)

            z, pred_next, score, det_logit = model(cur, action)
            z_next = model.encode(nxt)
            pred_loss = F.smooth_l1_loss(pred_next, z_next.detach())
            var_reg = 0.5 * (variance_loss(z) + variance_loss(z_next))
            cov_reg = 0.5 * (covariance_loss(z) + covariance_loss(z_next))
            rank_loss = base.pairwise_tail_rank_loss(score, y, ep, tw)
            reg_loss = base.regression_tail_loss(score, ylog, tw)
            tail_loss = reg_loss if rank_loss is None else rank_loss + TAIL_REG_WEIGHT * reg_loss
            det_loss = F.binary_cross_entropy_with_logits(det_logit, y_det)
            loss = (
                PRED_WEIGHT * pred_loss
                + VAR_WEIGHT * var_reg
                + COV_WEIGHT * cov_reg
                + TAIL_RANK_WEIGHT * tail_loss
                + DET_BCE_WEIGHT * det_loss
            )
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite native encoder loss")
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=5.0)
            opt.step()
        if device.type == "cuda" and epoch in (23, 47, 71):
            torch.cuda.empty_cache()
    model.eval()
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return model


base.configure_determinism = configure_determinism
base.variance_loss = variance_loss
base.covariance_loss = covariance_loss
base.train_native_encoder = train_native_encoder


def score_rows_integrated(
    model: G2NIntegratedModel,
    *,
    pixels: np.ndarray,
    device: torch.device,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    score = np.zeros(len(pixels), dtype=np.float64)
    det_logit = np.zeros(len(pixels), dtype=np.float64)
    latents = np.zeros((len(pixels), base.LATENT_DIM), dtype=np.float32)
    with torch.inference_mode():
        for lo in range(0, len(pixels), 256):
            hi = min(lo + 256, len(pixels))
            xb = torch.from_numpy(pixels[lo:hi].astype(np.float32, copy=False)).to(device)
            z = model.encode(xb)
            s = model.tail_head(z).squeeze(-1)
            d = model.det_head(z).squeeze(-1)
            latents[lo:hi] = z.detach().cpu().numpy().astype(np.float32)
            score[lo:hi] = s.detach().cpu().numpy().astype(np.float64)
            det_logit[lo:hi] = d.detach().cpu().numpy().astype(np.float64)
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return score, det_logit, latents


def ood_keep_mask(train_latents: np.ndarray, eval_latents: np.ndarray) -> tuple[np.ndarray, float]:
    train64 = train_latents.astype(np.float64)
    eval64 = eval_latents.astype(np.float64)
    mu = train64.mean(axis=0)
    var = train64.var(axis=0)
    train_dist = np.mean(((train64 - mu) ** 2) / (var + EPS), axis=1)
    eval_dist = np.mean(((eval64 - mu) ** 2) / (var + EPS), axis=1)
    threshold = float(np.percentile(train_dist, 99.0))
    return eval_dist <= threshold, threshold


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite float for JSON payload: {out!r}")
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


def health_verdict(stats: dict[str, float]) -> tuple[bool, str]:
    ok = (
        stats["var_mean"] >= HEALTH_VAR_MEAN_MIN
        and stats["var_min"] >= HEALTH_VAR_MIN_MIN
        and stats["effective_rank"] >= HEALTH_EFFECTIVE_RANK_MIN
    )
    reason = (
        f"var_mean={stats['var_mean']:.6g}, var_min={stats['var_min']:.6g}, "
        f"effective_rank={stats['effective_rank']:.6g}, thresholds "
        f"var_mean>={HEALTH_VAR_MEAN_MIN:g}, var_min>={HEALTH_VAR_MIN_MIN:g}, "
        f"effective_rank>={HEALTH_EFFECTIVE_RANK_MIN:g}"
    )
    return ok, reason


def make_fail_payload(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["allocation_delta", "auroc", "detection_auroc"],
        "reported_claim": f"fail-closed: {reason}",
    }


def build_claim(
    delta: dict[str, float],
    rho: dict[str, float],
    auroc: float,
    detection_auroc: float,
    stats: dict[str, float],
    verdict: str,
    ood_abstain_frac: float,
    device: torch.device,
) -> str:
    if verdict == "positive":
        decision = "CI high<0; criterion positive for this scoped 8GB runner"
        scale = "8GB scoped measurement"
    elif verdict == "negative":
        decision = "CI low>=0; healthy integrated latent did not beat uniform allocation"
        scale = "8GB non-break at this scale"
    else:
        decision = "CI crosses 0; allocation_delta is not identifiable"
        scale = "8GB non-break at this scale"
    if np.isfinite(rho["observed"]):
        rho_text = f"rho={rho['observed']:.6f} [{rho['low']:.6f},{rho['high']:.6f}]"
    else:
        rho_text = "rho=NA"
    return (
        f"G2N-v2 integrated encoder health: var_mean={stats['var_mean']:.6g}, "
        f"var_min={stats['var_min']:.6g}, effective_rank={stats['effective_rank']:.6g}. "
        f"allocation_delta={delta['observed']:.9g}, 95% CI=[{delta['low']:.9g},{delta['high']:.9g}], "
        f"{decision}. {rho_text}; tail_head h5/q75 AUROC={auroc:.6f}; "
        f"det_head h5/q75 detection_auroc={detection_auroc:.6f}; "
        f"ood_abstain_frac={ood_abstain_frac:.6f}. {FIXED_LEWM_CEILING_TEXT}. "
        f"Shared encoder saw pixels/actions plus train-split h5/q75 BCE labels and train-split allocation losses; "
        f"eval truth used only after health and OOD gates for final metrics; train/eval episodes isolated. "
        f"device={device.type}, 64px, batch={BATCH}, epochs={EPOCHS}, "
        f"VICReg variance/covariance weights={VAR_WEIGHT:g}/{COV_WEIGHT:g}, DET_BCE_WEIGHT={DET_BCE_WEIGHT:g}; {scale}."
    )


def build_payload(seed: int) -> dict[str, Any]:
    device = configure_determinism(seed)
    if not base.H5_PATH.exists() or not base.LABELS_PATH.exists():
        return make_fail_payload("missing _tworoom_prefix_large.h5 or g2n clean labels; var_mean/effective_rank unavailable")
    labels = base.load_npz(base.LABELS_PATH)
    required = [
        "train_anchor_ep_t0",
        "train_valid",
        "train_err_at_h",
        "train_mean_err_to_h",
        "train_y",
        "eval_anchor_ep_t0",
        "eval_valid",
        "eval_err_at_h",
        "eval_mean_err_to_h",
        "eval_y",
    ]
    missing = [k for k in required if k not in labels]
    if missing:
        return make_fail_payload("missing label fields: " + ",".join(missing) + "; var_mean/effective_rank unavailable")

    with base.h5py.File(base.H5_PATH, "r") as h5:
        ep_offset = np.asarray(h5["ep_offset"], dtype=np.int64)
        ep_len = np.asarray(h5["ep_len"], dtype=np.int64)

    train_valid = labels["train_valid"][:, base.TARGET_H_INDEX].astype(bool)
    eval_valid = labels["eval_valid"][:, base.TARGET_H_INDEX].astype(bool)
    if int(train_valid.sum()) == 0 or int(eval_valid.sum()) == 0:
        return make_fail_payload("empty h=5 train/eval anchors; var_mean/effective_rank unavailable")

    train_anchors = labels["train_anchor_ep_t0"][train_valid].astype(np.int64)
    eval_anchors = labels["eval_anchor_ep_t0"][eval_valid].astype(np.int64)
    train_current, train_next, train_next_valid = base.h5_frame_indices(train_anchors, ep_offset, ep_len)
    eval_current, _eval_next, _eval_next_valid = base.h5_frame_indices(eval_anchors, ep_offset, ep_len)
    train_current = train_current[train_next_valid]
    train_next = train_next[train_next_valid]
    train_anchors_for_data = train_anchors[train_next_valid]

    y_train_all = labels["train_mean_err_to_h"][train_valid, base.TARGET_H_INDEX].astype(np.float64)
    err_train_all = labels["train_err_at_h"][train_valid, : base.TARGET_H].astype(np.float64)
    y_det_all = labels["train_y"][train_valid][train_next_valid][:, base.TARGET_H_INDEX, base.Q75_INDEX]
    y_train = y_train_all[train_next_valid]
    y_det = y_det_all.astype(np.float32)
    cvar_train = np.max(err_train_all[train_next_valid], axis=1)
    if len(np.unique(train_anchors_for_data[:, 0])) < 2 or len(np.unique(eval_anchors[:, 0])) < 2:
        return make_fail_payload("too few episodes for episode bootstrap; var_mean/effective_rank unavailable")
    if not np.isfinite(y_train).all() or float(np.std(y_train)) == 0.0:
        return make_fail_payload("train h=5 target is not identifiable; var_mean/effective_rank unavailable")
    if not np.isfinite(y_det).all() or len(np.unique(y_det.astype(np.int8))) < 2:
        return make_fail_payload("train h=5/q75 detection target is not identifiable; var_mean/effective_rank unavailable")

    train_current_pixels = base.materialize_pixels(base.H5_PATH, train_current)
    train_next_pixels = base.materialize_pixels(base.H5_PATH, train_next)
    train_actions = base.materialize_actions(base.H5_PATH, train_current)
    eval_pixels = base.materialize_pixels(base.H5_PATH, eval_current)

    train_dataset = DetectionPixelRows(
        current_pixels=train_current_pixels,
        next_pixels=train_next_pixels,
        actions=train_actions,
        y_mean=y_train,
        y_log=np.log(y_train + EPS).astype(np.float32),
        episode=train_anchors_for_data[:, 0].astype(np.int64),
        tail_weight=base.tail_weights(cvar_train),
        y_det=y_det,
    )
    model = train_native_encoder(train_dataset, seed=seed + 1409, device=device)

    train_score, train_det_logit, train_latents = score_rows_integrated(
        model, pixels=train_current_pixels, device=device
    )
    del train_score, train_det_logit
    eval_score, eval_det_logit, eval_latents = score_rows_integrated(model, pixels=eval_pixels, device=device)
    stats = base.representation_stats(eval_latents)
    healthy, health_reason = health_verdict(stats)
    if not healthy:
        payload = make_fail_payload(
            "latent still collapsed or under-rank after strong VICReg, inconclusive; " + health_reason
        )
        if device.type == "cuda":
            torch.cuda.empty_cache()
        return payload

    keep_mask, ood_threshold = ood_keep_mask(train_latents, eval_latents)
    del ood_threshold
    ood_abstain_frac = float(1.0 - np.mean(keep_mask.astype(np.float64)))
    if int(keep_mask.sum()) == 0:
        return make_fail_payload(
            f"OOD fail-closed gate abstained on all eval anchors; ood_abstain_frac={ood_abstain_frac:.6f}"
        )

    kept_eval_anchors = eval_anchors[keep_mask]
    if len(np.unique(kept_eval_anchors[:, 0])) < 2:
        return make_fail_payload(
            f"too few kept eval episodes after OOD fail-closed gate; ood_abstain_frac={ood_abstain_frac:.6f}"
        )

    eval_errors_h5 = labels["eval_err_at_h"][eval_valid, : base.TARGET_H].astype(np.float64)[keep_mask]
    true_mean_h5 = labels["eval_mean_err_to_h"][eval_valid, base.TARGET_H_INDEX].astype(np.float64)[keep_mask]
    ep_eval = kept_eval_anchors[:, 0].astype(np.int64)
    kept_score = eval_score[keep_mask]
    kept_det_logit = eval_det_logit[keep_mask]

    by_ep = base.anchors_by_episode(kept_eval_anchors)
    uniform_alloc = base.summarize_allocation(base.allocation_uniform(by_ep), eval_errors_h5, kept_eval_anchors)
    native_alloc = base.summarize_allocation(
        base.allocation_by_score(kept_eval_anchors, by_ep, kept_score), eval_errors_h5, kept_eval_anchors
    )
    delta = base.paired_allocation_delta(native_alloc, uniform_alloc, seed=seed + BOOTSTRAP_SEED_OFFSET)
    rho = base.bootstrap_spearman(kept_score, true_mean_h5, ep_eval, seed=seed + BOOTSTRAP_SEED_OFFSET + 1)
    y_eval_q75 = labels["eval_y"][eval_valid, base.TARGET_H_INDEX, base.Q75_INDEX].astype(np.int8)[keep_mask]
    auroc = base.auroc_rank(y_eval_q75, kept_score)
    detection_auroc = base.auroc_rank(y_eval_q75, kept_det_logit)
    verdict = base.verdict_from_delta(delta["low"], delta["high"])

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": float(delta["observed"]),
        "ci": {"low": float(delta["low"]), "high": float(delta["high"])},
        "measured_scope": ["allocation_delta", "auroc", "detection_auroc"],
        "reported_claim": build_claim(delta, rho, auroc, detection_auroc, stats, verdict, ood_abstain_frac, device),
    }
    if verdict == "unidentifiable":
        payload["status"] = "fail-closed"
    if device.type == "cuda":
        torch.cuda.empty_cache()
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = clean_json(build_payload(int(args.seed)))
    claim = str(payload.get("reported_claim", ""))
    lowered = claim.lower()
    if any(token in claim or token in lowered for token in FORBIDDEN_CLAIM_TOKENS):
        raise RuntimeError("reported_claim contains a forbidden scope or claim token")
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
