from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import h5py
import hdf5plugin  # noqa: F401 - registers blosc HDF5 filter
import numpy as np
import torch
import torch.nn.functional as F
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _phase1c_gap_ledger import (
    BOOTSTRAP_SEED,
    DISTINCTIONS,
    FEATURE_VARIANTS,
    LogisticHead,
    auroc_rank,
    basic_metrics,
    bootstrap_metrics_by_episode,
    build_gap_features,
    distinction_truth,
    fit_linear_r2_quality,
    fit_logistic_head,
    flatten_transition_rows,
    fmt_ci,
    predict_logistic_head,
    split_episodes,
)


ROOT = Path(__file__).resolve().parent
NPZ_PATH = ROOT / "tworooms_latent_large.npz"
H5_PATH = ROOT / "_tworoom_prefix_large.h5"
REPORT_DIR = ROOT / "reports"
JSON_PATH = REPORT_DIR / "lewm_brittleness_gap.json"
MD_PATH = REPORT_DIR / "lewm_brittleness_gap.md"
FINDINGS_PATH = ROOT / "PHASE2A_FINDINGS.md"
DEMO_PATH = REPORT_DIR / "brittleness_demo_samples.npz"

MODEL_REPO = "quentinll/lewm-tworooms"
IMAGENET_MEAN = np.array([0.485, 0.456, 0.406], dtype=np.float32)
IMAGENET_STD = np.array([0.229, 0.224, 0.225], dtype=np.float32)

PRIMARY_VARIANT = "B_denoised_agent_room_only"
PRIMARY_PROBE_INDICES = FEATURE_VARIANTS[PRIMARY_VARIANT]
BOOTSTRAPS = 300


def to_model_pixels(frames: np.ndarray, image_size: int, device: torch.device) -> torch.Tensor:
    x = torch.from_numpy(frames).to(device=device, dtype=torch.float32)
    x = x.permute(0, 3, 1, 2).div_(255.0)
    mean = torch.tensor(IMAGENET_MEAN, device=device).view(1, 3, 1, 1)
    std = torch.tensor(IMAGENET_STD, device=device).view(1, 3, 1, 1)
    x = (x - mean) / std
    if x.shape[-2:] != (image_size, image_size):
        x = F.interpolate(x, size=(image_size, image_size), mode="bilinear", align_corners=False)
    return x


def perturb_frames(frames_u8: np.ndarray, family: str, strength: float) -> np.ndarray:
    if strength == 0.0:
        return frames_u8.copy()

    x = frames_u8.astype(np.float32)
    if family == "color_shift":
        factors = np.array([1.0 + strength, 1.0 + 0.5 * strength, max(0.0, 1.0 - strength)], dtype=np.float32)
        x = x * factors.reshape(1, 1, 1, 3)
    elif family == "brightness":
        x = x * (1.0 + strength)
    elif family == "background_tint":
        tint = np.array([80.0 * strength, 20.0 * strength, -35.0 * strength], dtype=np.float32)
        subject = approximate_subject_mask(x)
        x = x + (~subject)[..., None].astype(np.float32) * tint.reshape(1, 1, 1, 3)
    elif family == "occlusion":
        frac = float(strength)
        h, w = x.shape[1], x.shape[2]
        side = max(1, int(round(min(h, w) * frac)))
        y0 = max(0, (h - side) // 2)
        x0 = max(0, (w - side) // 2)
        fill = np.array([24.0, 24.0, 24.0], dtype=np.float32)
        x[:, y0 : y0 + side, x0 : x0 + side, :] = fill.reshape(1, 1, 1, 3)
    elif family == "gaussian_noise":
        rng = np.random.default_rng(777_000 + int(round(strength * 1000)))
        x = x + rng.normal(0.0, strength, size=x.shape).astype(np.float32)
    else:
        raise ValueError(f"unknown perturbation family: {family}")

    return np.clip(x, 0.0, 255.0).astype(np.uint8)


def approximate_subject_mask(x: np.ndarray) -> np.ndarray:
    # Simple RGB edge/color heuristic, then one-pixel dilation. Used only to avoid
    # tinting the most visually salient foreground when exact simulator masks are unavailable.
    channel_range = x.max(axis=-1) - x.min(axis=-1)
    gray = x.mean(axis=-1)
    gx = np.abs(gray[:, :, 1:] - gray[:, :, :-1])
    gy = np.abs(gray[:, 1:, :] - gray[:, :-1, :])
    edge = np.zeros_like(gray, dtype=np.float32)
    edge[:, :, 1:] = np.maximum(edge[:, :, 1:], gx)
    edge[:, 1:, :] = np.maximum(edge[:, 1:, :], gy)
    threshold = np.percentile(edge.reshape(edge.shape[0], -1), 90.0, axis=1).reshape(-1, 1, 1)
    mask = (edge >= threshold) | (channel_range > 55.0)
    dilated = mask.copy()
    for dy in (-1, 0, 1):
        for dx in (-1, 0, 1):
            dilated |= np.roll(np.roll(mask, dy, axis=1), dx, axis=2)
    return dilated


def perturbation_grid() -> dict[str, list[float]]:
    return {
        "color_shift": [0.0, 0.1, 0.2, 0.3, 0.4],
        "occlusion": [0.0, 0.12, 0.20, 0.28, 0.36],
        "brightness": [0.0, 0.1, 0.2, 0.3, 0.4],
        "background_tint": [0.0, 0.15, 0.30, 0.45, 0.60],
        "gaussian_noise": [0.0, 5.0, 10.0, 15.0, 25.0],
    }


def clean_json(v: Any) -> Any:
    if isinstance(v, dict):
        return {str(k): clean_json(val) for k, val in v.items()}
    if isinstance(v, (list, tuple)):
        return [clean_json(val) for val in v]
    if isinstance(v, np.ndarray):
        return clean_json(v.tolist())
    if isinstance(v, (np.integer,)):
        return int(v)
    if isinstance(v, (np.floating,)):
        v = float(v)
    if isinstance(v, float) and not math.isfinite(v):
        return None
    return v


def bootstrap_scalar_by_episode(
    values: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> dict[str, float]:
    observed = float(np.mean(values)) if len(values) else float("nan")
    rng = np.random.default_rng(seed)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    samples = []
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        samples.append(float(np.mean(values[idx])))
    arr = np.asarray(samples, dtype=np.float64)
    return {
        "observed": observed,
        "bootstrap_mean": float(np.nanmean(arr)),
        "ci95_low": float(np.nanpercentile(arr, 2.5)),
        "ci95_high": float(np.nanpercentile(arr, 97.5)),
    }


def perturb_metrics(
    y_err: np.ndarray,
    gap_score: np.ndarray,
    prediction_mse: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> dict[str, dict[str, float]]:
    gap_as_critical = gap_score
    out = bootstrap_metrics_by_episode(
        y_err.astype(np.int8),
        gap_score.astype(np.float64),
        gap_as_critical.astype(np.float64),
        episode.astype(np.int64),
        seed=seed,
        n_boot=n_boot,
    )
    out["vanilla_uer"] = bootstrap_scalar_by_episode(
        y_err.astype(np.float64), episode, seed=seed + 303, n_boot=n_boot
    )
    out["bedc_gap_head_uer"] = out["unlogged_error_rate"]
    out["mean_prediction_mse"] = bootstrap_scalar_by_episode(
        prediction_mse.astype(np.float64), episode, seed=seed + 101, n_boot=n_boot
    )
    out["mean_gap_score"] = bootstrap_scalar_by_episode(
        gap_score.astype(np.float64), episode, seed=seed + 202, n_boot=n_boot
    )
    out["median_prediction_mse_observed"] = {
        "observed": float(np.median(prediction_mse)),
        "bootstrap_mean": float("nan"),
        "ci95_low": float("nan"),
        "ci95_high": float("nan"),
    }
    return out


def fit_clean_protocol(data: dict[str, np.ndarray], rows: dict[str, np.ndarray]) -> dict[str, Any]:
    splits_ep = split_episodes(data["emb"].shape[0])
    split_masks = {name: np.isin(rows["episode"], eps) for name, eps in splits_ep.items()}
    train_mask = split_masks["train"]
    cal_mask = split_masks["calibration"]
    eval_mask = split_masks["eval"]

    debts: list[dict[str, str]] = [
        {
            "type": "coverage_debt",
            "source": "statistical_design",
            "detail": (
                f"single LeWM tworooms latent export with {data['emb'].shape[0]} episodes/"
                f"{len(rows['episode'])} transitions; episode bootstrap does not replace independent world seeds"
            ),
        }
    ]

    near_threshold = float(np.median(rows["distance_to_target"][train_mask]))
    y_dist = distinction_truth(rows, near_threshold, prefix="")

    probe_heads: dict[str, LogisticHead] = {}
    probe_report: dict[str, Any] = {}
    probe_prob_cols = []
    probe_logit_cols = []
    probe_pred_cols = []
    for j, name in enumerate(DISTINCTIONS):
        head, info = fit_logistic_head(rows["emb"][train_mask], y_dist[train_mask, j], steps=700, lr=0.18, l2=1e-4)
        probe_heads[name] = head
        p_all, logit_all = predict_logistic_head(head, rows["emb"])
        pred_all = (p_all >= 0.5).astype(np.float64)
        probe_prob_cols.append(p_all)
        probe_logit_cols.append(logit_all)
        probe_pred_cols.append(pred_all)
        eval_acc = float(np.mean(pred_all[eval_mask] == y_dist[eval_mask, j]))
        if eval_acc < 0.60:
            debts.append(
                {
                    "type": "source_debt",
                    "source": f"distinction_probe:{name}",
                    "detail": f"eval accuracy {eval_acc:.4f} below 0.60 separability sanity threshold",
                }
            )
        probe_report[name] = {
            "train_label_rate": float(y_dist[train_mask, j].mean()),
            "calibration_label_rate": float(y_dist[cal_mask, j].mean()),
            "eval_label_rate": float(y_dist[eval_mask, j].mean()),
            "train_accuracy": float(np.mean(pred_all[train_mask] == y_dist[train_mask, j])),
            "calibration_accuracy": float(np.mean(pred_all[cal_mask] == y_dist[cal_mask, j])),
            "eval_accuracy": eval_acc,
            "fit": info,
        }

    probe_prob = np.stack(probe_prob_cols, axis=1)
    probe_logit = np.stack(probe_logit_cols, axis=1)
    probe_pred = np.stack(probe_pred_cols, axis=1)

    quality_feature, quality_report = fit_linear_r2_quality(
        rows["emb"][train_mask],
        rows["observation"][train_mask],
        rows["emb"][eval_mask],
        rows["observation"][eval_mask],
    )
    x_b, _ = build_gap_features(rows["emb"], probe_prob, probe_logit, probe_pred, quality_feature, PRIMARY_PROBE_INDICES)

    tau_err = float(np.percentile(rows["mse"][train_mask], 75))
    y_prediction_error = (rows["mse"] > tau_err).astype(np.int8)
    head, fit_info = fit_logistic_head(
        x_b[train_mask],
        y_prediction_error[train_mask],
        steps=500,
        lr=0.14,
        l2=1e-4,
    )
    clean_gap_score, _ = predict_logistic_head(head, x_b)

    clean_eval_metrics = perturb_metrics(
        y_prediction_error[eval_mask],
        clean_gap_score[eval_mask],
        rows["mse"][eval_mask],
        rows["episode"][eval_mask],
        seed=BOOTSTRAP_SEED,
        n_boot=BOOTSTRAPS,
    )

    return {
        "splits_ep": splits_ep,
        "split_masks": split_masks,
        "train_mask": train_mask,
        "cal_mask": cal_mask,
        "eval_mask": eval_mask,
        "near_threshold": near_threshold,
        "probe_heads": probe_heads,
        "probe_report": probe_report,
        "quality_feature": quality_feature,
        "quality_report": quality_report,
        "tau_err": tau_err,
        "gap_head": head,
        "gap_head_fit": fit_info,
        "clean_gap_score": clean_gap_score,
        "clean_y_prediction_error": y_prediction_error,
        "clean_eval_metrics": clean_eval_metrics,
        "debts": debts,
    }


def encode_eval_episodes(
    h5: h5py.File,
    model: Any,
    config: dict[str, Any],
    data: dict[str, np.ndarray],
    eval_eps: np.ndarray,
    family: str,
    strength: float,
    device: torch.device,
) -> dict[int, np.ndarray]:
    image_size = int(config["encoder"]["image_size"])
    out: dict[int, np.ndarray] = {}
    with torch.inference_mode():
        for ep in eval_eps:
            ep = int(ep)
            valid_t = int(data["valid_mask"][ep].sum())
            idx = data["raw_frame_idx"][ep, :valid_t].astype(np.int64)
            frames = h5["pixels"][idx]
            frames = perturb_frames(frames, family, strength)
            pixels = to_model_pixels(frames, image_size=image_size, device=device)
            emb = model.encode({"pixels": pixels.unsqueeze(0)})["emb"][0].detach().cpu().numpy()
            out[ep] = emb.astype(np.float32)
    return out


def predict_eval_rows(
    model: Any,
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    eval_rows_idx: np.ndarray,
    pert_emb_by_ep: dict[int, np.ndarray],
    device: torch.device,
    *,
    batch_size: int,
) -> tuple[np.ndarray, np.ndarray]:
    history_size = int(np.asarray(data["history_size"]).item())
    windows_emb = []
    windows_act = []
    positions = []
    valid_eval_rows = []
    for row_idx in eval_rows_idx:
        ep = int(rows["episode"][row_idx])
        t = int(rows["t"][row_idx])
        start = 0 if t < history_size else t - history_size + 1
        pos = t - start
        e = pert_emb_by_ep[ep][start : start + history_size]
        a = data["action"][ep, start : start + history_size]
        if e.shape[0] != history_size or a.shape[0] != history_size or not np.isfinite(e).all() or not np.isfinite(a).all():
            continue
        windows_emb.append(e)
        windows_act.append(a)
        positions.append(pos)
        valid_eval_rows.append(row_idx)

    pred = np.zeros((len(valid_eval_rows), data["emb"].shape[-1]), dtype=np.float32)
    with torch.inference_mode():
        for lo in range(0, len(valid_eval_rows), batch_size):
            hi = min(lo + batch_size, len(valid_eval_rows))
            be = torch.from_numpy(np.stack(windows_emb[lo:hi])).to(device=device, dtype=torch.float32)
            ba = torch.from_numpy(np.stack(windows_act[lo:hi])).to(device=device, dtype=torch.float32)
            bp = model.predict(be, model.action_encoder(ba)).detach().cpu().numpy()
            for j, pos in enumerate(positions[lo:hi]):
                pred[lo + j] = bp[j, pos]

    target = np.zeros_like(pred)
    for i, row_idx in enumerate(valid_eval_rows):
        ep = int(rows["episode"][row_idx])
        t = int(rows["t"][row_idx])
        target[i] = pert_emb_by_ep[ep][t + 1]
    mse = ((pred - target) ** 2).mean(axis=1).astype(np.float64)
    return np.asarray(valid_eval_rows, dtype=np.int64), mse


def score_gap_on_eval_rows(
    protocol: dict[str, Any],
    rows: dict[str, np.ndarray],
    eval_rows_idx: np.ndarray,
    pert_emb: np.ndarray,
) -> np.ndarray:
    probe_prob_cols = []
    probe_logit_cols = []
    probe_pred_cols = []
    for name in DISTINCTIONS:
        p, logit = predict_logistic_head(protocol["probe_heads"][name], pert_emb.astype(np.float64))
        probe_prob_cols.append(p)
        probe_logit_cols.append(logit)
        probe_pred_cols.append((p >= 0.5).astype(np.float64))
    probe_prob = np.stack(probe_prob_cols, axis=1)
    probe_logit = np.stack(probe_logit_cols, axis=1)
    probe_pred = np.stack(probe_pred_cols, axis=1)
    x_b, _ = build_gap_features(
        pert_emb.astype(np.float64),
        probe_prob,
        probe_logit,
        probe_pred,
        protocol["quality_feature"],
        PRIMARY_PROBE_INDICES,
    )
    gap_score, _ = predict_logistic_head(protocol["gap_head"], x_b)
    if len(gap_score) != len(eval_rows_idx):
        raise RuntimeError("gap score and eval row length mismatch")
    return gap_score.astype(np.float64)


def make_demo_samples(
    h5: h5py.File,
    rows: dict[str, np.ndarray],
    data: dict[str, np.ndarray],
    samples: list[dict[str, Any]],
) -> None:
    if not samples:
        return
    originals = []
    perturbed = []
    family = []
    strength = []
    episode = []
    t_idx = []
    prediction_mse = []
    gap_score = []
    for s in samples[:12]:
        ep = int(s["episode"])
        t = int(s["t"])
        frame_idx = int(data["raw_frame_idx"][ep, t])
        orig = h5["pixels"][frame_idx : frame_idx + 1]
        pert = perturb_frames(orig, s["family"], float(s["strength"]))
        originals.append(orig[0])
        perturbed.append(pert[0])
        family.append(s["family"])
        strength.append(float(s["strength"]))
        episode.append(ep)
        t_idx.append(t)
        prediction_mse.append(float(s["prediction_mse"]))
        gap_score.append(float(s["gap_score"]))
    np.savez_compressed(
        DEMO_PATH,
        original_frame=np.stack(originals),
        perturbed_frame=np.stack(perturbed),
        family=np.asarray(family),
        strength=np.asarray(strength, dtype=np.float32),
        episode=np.asarray(episode, dtype=np.int64),
        t=np.asarray(t_idx, dtype=np.int64),
        prediction_mse=np.asarray(prediction_mse, dtype=np.float32),
        gap_score=np.asarray(gap_score, dtype=np.float32),
    )


def evaluate_family_strength(
    h5: h5py.File,
    model: Any,
    config: dict[str, Any],
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    protocol: dict[str, Any],
    family: str,
    strength: float,
    device: torch.device,
    *,
    batch_size: int,
    bootstrap_seed: int,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    eval_mask = protocol["eval_mask"]
    eval_rows_idx = np.where(eval_mask)[0]
    eval_eps = protocol["splits_ep"]["eval"]

    if strength == 0.0:
        valid_rows_idx = eval_rows_idx
        prediction_mse = rows["mse"][eval_mask].astype(np.float64)
        gap_score = protocol["clean_gap_score"][eval_mask].astype(np.float64)
        source = "cached_clean_latents"
    else:
        pert_emb_by_ep = encode_eval_episodes(h5, model, config, data, eval_eps, family, strength, device)
        valid_rows_idx, prediction_mse = predict_eval_rows(
            model,
            data,
            rows,
            eval_rows_idx,
            pert_emb_by_ep,
            device,
            batch_size=batch_size,
        )
        current_emb = np.stack([pert_emb_by_ep[int(rows["episode"][i])][int(rows["t"][i])] for i in valid_rows_idx])
        gap_score = score_gap_on_eval_rows(protocol, rows, valid_rows_idx, current_emb)
        source = "perturbed_rgb_reencoded"

    y_err = (prediction_mse > protocol["tau_err"]).astype(np.int8)
    episode = rows["episode"][valid_rows_idx].astype(np.int64)
    metrics = perturb_metrics(
        y_err,
        gap_score,
        prediction_mse,
        episode,
        seed=bootstrap_seed,
        n_boot=BOOTSTRAPS,
    )
    observed = basic_metrics(y_err, gap_score, gap_score)

    demo: list[dict[str, Any]] = []
    if strength != 0.0:
        order = np.argsort(-prediction_mse)
        for j in order[:2]:
            row_idx = int(valid_rows_idx[j])
            demo.append(
                {
                    "family": family,
                    "strength": float(strength),
                    "episode": int(rows["episode"][row_idx]),
                    "t": int(rows["t"][row_idx]),
                    "prediction_mse": float(prediction_mse[j]),
                    "gap_score": float(gap_score[j]),
                }
            )

    result = {
        "family": family,
        "strength": float(strength),
        "source": source,
        "sample_count": int(len(valid_rows_idx)),
        "episode_count": int(len(np.unique(episode))),
        "failure_threshold_clean_train_p75": float(protocol["tau_err"]),
        "observed": {
            "mean_prediction_mse": float(np.mean(prediction_mse)),
            "median_prediction_mse": float(np.median(prediction_mse)),
            "failure_rate_vanilla_uer": float(np.mean(y_err)),
            "bedc_gap_head_uer": float(np.mean((y_err > 0) & (gap_score < 0.5))),
            "failure_detection_auroc": float(auroc_rank(y_err, gap_score)),
            "mean_gap_score": float(np.mean(gap_score)),
            "declared_gap_rate": float(np.mean(gap_score >= 0.5)),
            "logged_given_failure_rate": float(np.mean(gap_score[y_err > 0] >= 0.5)) if np.any(y_err) else float("nan"),
        },
        "metrics_episode_bootstrap": metrics,
        "raw_basic_metrics": observed,
    }
    return result, demo


def summarize_family(points: list[dict[str, Any]]) -> dict[str, Any]:
    strengths = [p["strength"] for p in points]
    mean_mse = [p["observed"]["mean_prediction_mse"] for p in points]
    vanilla = [p["observed"]["failure_rate_vanilla_uer"] for p in points]
    bedc = [p["observed"]["bedc_gap_head_uer"] for p in points]
    auroc = [p["observed"]["failure_detection_auroc"] for p in points]
    nonzero_auroc = [a for s, a in zip(strengths, auroc) if s != 0.0]
    return {
        "strengths": strengths,
        "mean_prediction_mse": mean_mse,
        "vanilla_uer": vanilla,
        "bedc_gap_head_uer": bedc,
        "failure_detection_auroc": auroc,
        "predictor_error_final_minus_clean": float(mean_mse[-1] - mean_mse[0]),
        "vanilla_uer_final_minus_clean": float(vanilla[-1] - vanilla[0]),
        "bedc_uer_final_minus_vanilla_final": float(bedc[-1] - vanilla[-1]),
        "predictor_error_monotone_non_decreasing": bool(all(b >= a - 1e-12 for a, b in zip(mean_mse, mean_mse[1:]))),
        "vanilla_uer_monotone_non_decreasing": bool(all(b >= a - 1e-12 for a, b in zip(vanilla, vanilla[1:]))),
        "min_nonzero_auroc": float(min(nonzero_auroc)) if nonzero_auroc else float("nan"),
        "claim": (
            "positive"
            if mean_mse[-1] > mean_mse[0]
            and vanilla[-1] > vanilla[0]
            and bedc[-1] < vanilla[-1]
            and nonzero_auroc
            and min(nonzero_auroc) > 0.5
            else "negative_or_inconclusive"
        ),
    }


def write_reports(report: dict[str, Any]) -> None:
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")

    lines = [
        "# Phase 2a: brittleness gap ledger",
        "",
        f"- latent: `tworooms_latent_large.npz`; H5: `_tworoom_prefix_large.h5`",
        f"- protocol: clean train split fits probe + `{PRIMARY_VARIANT}` prediction_error gap head; perturbed eval is OOD only",
        f"- failure truth: `prediction_mse > {report['clean_protocol']['failure_threshold_clean_train_p75']:.6f}` (clean train p75)",
        f"- bootstrap: {BOOTSTRAPS} resamples, eval episodes as unit",
        f"- conclusion: **{report['conclusion']['claim']}** - {report['conclusion']['summary']}",
        "",
        "## Curves",
        "",
    ]
    for family, pack in report["families"].items():
        summary = pack["summary"]
        lines.extend(
            [
                f"### {family}",
                "",
                f"- claim: **{summary['claim']}**; final mse-clean delta={summary['predictor_error_final_minus_clean']:.6f}; final vanilla UER-clean delta={summary['vanilla_uer_final_minus_clean']:.4f}; final BEDC-vs-vanilla UER delta={summary['bedc_uer_final_minus_vanilla_final']:.4f}; min nonzero AUROC={summary['min_nonzero_auroc']:.4f}",
                "",
                "| strength | mean MSE | vanilla UER | BEDC UER | AUROC | mean gap |",
                "|---:|---:|---:|---:|---:|---:|",
            ]
        )
        for point in pack["points"]:
            obs = point["observed"]
            lines.append(
                f"| {point['strength']:.3g} | {obs['mean_prediction_mse']:.6f} | "
                f"{obs['failure_rate_vanilla_uer']:.4f} | {obs['bedc_gap_head_uer']:.4f} | "
                f"{obs['failure_detection_auroc']:.4f} | {obs['mean_gap_score']:.4f} |"
            )
        lines.append("")

    lines.extend(["## CI Detail", ""])
    for family, pack in report["families"].items():
        lines.append(f"### {family}")
        lines.append("")
        lines.append("| strength | mean MSE CI | vanilla UER CI | BEDC UER CI | AUROC CI |")
        lines.append("|---:|---:|---:|---:|---:|")
        for point in pack["points"]:
            m = point["metrics_episode_bootstrap"]
            lines.append(
                f"| {point['strength']:.3g} | {fmt_ci(m['mean_prediction_mse'])} | "
                f"{fmt_ci(m['vanilla_uer'])} | {fmt_ci(m['bedc_gap_head_uer'])} | "
                f"{fmt_ci(m['failure_detection_auroc'])} |"
            )
        lines.append("")

    lines.extend(["## Debt", ""])
    for d in report["debt"]:
        lines.append(f"- {d['type']} / {d['source']}: {d['detail']}")
    lines.append("")
    lines.append(f"Demo samples: `{DEMO_PATH.as_posix()}`" if report["demo_samples_written"] else "Demo samples: not written")
    lines.append("")
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")

    findings = [
        "# PHASE2A_FINDINGS",
        "",
        "## 结论",
        "",
        f"本轮结论：**{report['conclusion']['claim']}**。{report['conclusion']['summary']}",
        "",
        "判据采用 clean train split 训练 probe 与 gap head，所有扰动只在 eval episodes 上重编码评估；failure truth 固定为 clean train `prediction_mse` p75 阈值。",
        "",
        "## 核心数值",
        "",
    ]
    for family, pack in report["families"].items():
        summary = pack["summary"]
        last = pack["points"][-1]
        obs = last["observed"]
        findings.extend(
            [
                f"### {family}",
                "",
                f"- family claim: **{summary['claim']}**",
                f"- error delta(final-clean): {summary['predictor_error_final_minus_clean']:.6f}; monotone={summary['predictor_error_monotone_non_decreasing']}",
                f"- vanilla UER delta(final-clean): {summary['vanilla_uer_final_minus_clean']:.4f}; monotone={summary['vanilla_uer_monotone_non_decreasing']}",
                f"- final vanilla UER: {obs['failure_rate_vanilla_uer']:.4f}; final BEDC UER: {obs['bedc_gap_head_uer']:.4f}; final AUROC: {obs['failure_detection_auroc']:.4f}",
                f"- min nonzero AUROC: {summary['min_nonzero_auroc']:.4f}",
                "",
            ]
        )
    findings.extend(["## Debt", ""])
    for d in report["debt"]:
        findings.append(f"- {d['type']} / {d['source']}: {d['detail']}")
    findings.extend(
        [
            "",
            "## 下一步",
            "",
            "- 若某些扰动族为 negative_or_inconclusive，应进入 OOD-aware gap training：把扰动类型/强度纳入 gap calibration，而不是把 clean-only head 的外推能力作为默认假设。",
            "- 当前统计单位仍是单 export 内 episode bootstrap；独立 world seeds 仍是下一阶段需要补的统计 debt。",
            "",
            f"产物：`{JSON_PATH.as_posix()}`、`{MD_PATH.as_posix()}`、`{DEMO_PATH.as_posix()}`。",
            "",
        ]
    )
    FINDINGS_PATH.write_text("\n".join(findings), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--families", nargs="*", default=None)
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    parser.add_argument("--predict-batch", type=int, default=512)
    args = parser.parse_args()

    REPORT_DIR.mkdir(exist_ok=True)
    device = torch.device(args.device)
    grids = perturbation_grid()
    families = args.families if args.families else list(grids)
    for family in families:
        if family not in grids:
            raise ValueError(f"unknown family {family}; choices={sorted(grids)}")

    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    rows = flatten_transition_rows(data)
    protocol = fit_clean_protocol(data, rows)

    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    model = build_model(config)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)

    family_reports: dict[str, Any] = {}
    demo_samples: list[dict[str, Any]] = []
    with h5py.File(H5_PATH, "r") as h5:
        for family_i, family in enumerate(families):
            points = []
            for strength_i, strength in enumerate(grids[family]):
                print(f"evaluating {family} strength={strength}", flush=True)
                point, demo = evaluate_family_strength(
                    h5,
                    model,
                    config,
                    data,
                    rows,
                    protocol,
                    family,
                    float(strength),
                    device,
                    batch_size=args.predict_batch,
                    bootstrap_seed=BOOTSTRAP_SEED + 1000 * family_i + strength_i,
                )
                points.append(point)
                demo_samples.extend(demo)
            family_reports[family] = {"points": points, "summary": summarize_family(points)}
        make_demo_samples(h5, rows, data, demo_samples)

    positive = [name for name, pack in family_reports.items() if pack["summary"]["claim"] == "positive"]
    negative = [name for name, pack in family_reports.items() if pack["summary"]["claim"] != "positive"]
    if len(positive) == len(family_reports):
        claim = "positive"
        summary = "all evaluated perturbation families show higher predictor error/vanilla UER under stronger perturbation, while the clean-trained BEDC gap head lowers UER and keeps AUROC above 0.5"
    elif positive:
        claim = "mixed"
        summary = f"positive on {positive}; fail-closed negative_or_inconclusive on {negative}"
    else:
        claim = "negative_or_inconclusive"
        summary = "clean-trained BEDC gap head did not establish the full brittleness-detection claim under the evaluated OOD perturbations"

    report = {
        "protocol": "Phase 2a brittleness gap ledger: clean-trained Phase 1c B prediction_error head evaluated on perturbed tworooms RGB frames",
        "families_evaluated": families,
        "clean_protocol": {
            "primary_variant": PRIMARY_VARIANT,
            "failure_threshold_clean_train_p75": float(protocol["tau_err"]),
            "gap_head_fit": protocol["gap_head_fit"],
            "clean_eval_metrics": protocol["clean_eval_metrics"],
            "split": {
                name: {
                    "episode_count": int(len(eps)),
                    "transition_count": int(protocol["split_masks"][name].sum()),
                }
                for name, eps in protocol["splits_ep"].items()
            },
            "distinction_probe_report": protocol["probe_report"],
            "identifiability_proxy": protocol["quality_report"],
        },
        "perturbation_grid": grids,
        "families": family_reports,
        "conclusion": {"claim": claim, "summary": summary, "positive_families": positive, "negative_families": negative},
        "debt": protocol["debts"]
        + [
            {
                "type": "source_debt",
                "source": "background_tint_mask",
                "detail": "background_tint uses RGB edge/color heuristic foreground mask, not simulator segmentation; failures are reported fail-closed",
            }
        ],
        "bootstrap": {"resamples": BOOTSTRAPS, "unit": "eval episodes", "seed_base": BOOTSTRAP_SEED},
        "demo_samples_written": DEMO_PATH.exists(),
    }

    write_reports(report)
    print(json.dumps(clean_json(report["conclusion"]), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)
    print(f"wrote {FINDINGS_PATH}", flush=True)
    if DEMO_PATH.exists():
        print(f"wrote {DEMO_PATH}", flush=True)


if __name__ == "__main__":
    main()
