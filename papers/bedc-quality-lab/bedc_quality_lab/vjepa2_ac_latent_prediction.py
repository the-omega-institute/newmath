"""MiniGrid latent-prediction contact for the public V-JEPA2-AC checkpoint."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import traceback
from typing import Any

import numpy as np

from bedc_quality_lab.public_jepa_baselines import _cuda_environment_report, _load_vjepa2_ac_giant_modules
from bedc_quality_lab.public_minigrid_native_benchmark import DEFAULT_ENVIRONMENT_ID
from bedc_quality_lab.vjepa2_ac_claim_certificate import (
    _collect_minigrid_transitions,
    _extract_features,
)


def _dependency_status() -> dict[str, str]:
    return {
        name: "installed" if importlib.util.find_spec(name) is not None else "missing"
        for name in ("gymnasium", "minigrid", "torch", "timm", "einops")
    }


def _safe_corrcoef(left: np.ndarray, right: np.ndarray) -> float:
    left_arr = np.asarray(left, dtype=np.float64).reshape(-1)
    right_arr = np.asarray(right, dtype=np.float64).reshape(-1)
    if left_arr.size == 0 or right_arr.size == 0:
        return 0.0
    left_std = float(np.std(left_arr))
    right_std = float(np.std(right_arr))
    if left_std == 0.0 or right_std == 0.0:
        return 0.0
    return float(np.corrcoef(left_arr, right_arr)[0, 1])


def _fit_linear_map(source: np.ndarray, target: np.ndarray, *, ridge: float = 1e-3) -> np.ndarray:
    source_arr = np.asarray(source, dtype=np.float64)
    target_arr = np.asarray(target, dtype=np.float64)
    design = np.column_stack([source_arr, np.ones(source_arr.shape[0])])
    gram = design.T @ design + ridge * np.eye(design.shape[1])
    rhs = design.T @ target_arr
    return np.linalg.solve(gram, rhs)


def _predict_linear_map(source: np.ndarray, weights: np.ndarray) -> np.ndarray:
    source_arr = np.asarray(source, dtype=np.float64)
    design = np.column_stack([source_arr, np.ones(source_arr.shape[0])])
    return design @ weights


def _r2_score(predicted: np.ndarray, target: np.ndarray) -> float:
    predicted_arr = np.asarray(predicted, dtype=np.float64)
    target_arr = np.asarray(target, dtype=np.float64)
    residual = float(np.sum((target_arr - predicted_arr) ** 2))
    centered = float(np.sum((target_arr - np.mean(target_arr, axis=0, keepdims=True)) ** 2))
    if centered == 0.0:
        return 0.0
    return float(1.0 - residual / centered)


def build_vjepa2_ac_latent_prediction_packet(
    *,
    source_features: np.ndarray,
    predicted_features: np.ndarray,
    train_count: int,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
    carrier_id: str = "vjepa2-ac-giant-fixed-minigrid-carrier",
    torch_environment: dict[str, Any] | None = None,
    dependency_status: dict[str, str] | None = None,
) -> dict[str, Any]:
    source = np.asarray(source_features, dtype=np.float64)
    predicted = np.asarray(predicted_features, dtype=np.float64)
    if source.shape != predicted.shape:
        raise ValueError("source_features and predicted_features must have the same shape")
    if source.ndim != 2:
        raise ValueError("features must be matrices")
    if not 1 <= int(train_count) < source.shape[0]:
        raise ValueError("train_count must leave at least one test row")

    train = int(train_count)
    source_train = source[:train]
    predicted_train = predicted[:train]
    source_test = source[train:]
    predicted_test = predicted[train:]

    weights = _fit_linear_map(predicted_train, source_train)
    aligned = _predict_linear_map(predicted_test, weights)
    mse = float(np.mean((aligned - source_test) ** 2))
    baseline = np.repeat(np.mean(source_train, axis=0, keepdims=True), source_test.shape[0], axis=0)
    baseline_mse = float(np.mean((baseline - source_test) ** 2))
    r2 = _r2_score(aligned, source_test)
    cosine_den = np.linalg.norm(aligned, axis=1) * np.linalg.norm(source_test, axis=1)
    cosine = np.divide(
        np.sum(aligned * source_test, axis=1),
        np.maximum(cosine_den, 1e-12),
    )
    latent_prediction_score = float(max(0.0, min(1.0, 1.0 - mse / max(baseline_mse, 1e-12))))
    return {
        "schema_id": "bedc-vjepa2-ac-minigrid-latent-prediction",
        "status": "executed",
        "candidate_id": "vjepa2-ac-vit-giant",
        "carrier_id": carrier_id,
        "environment_id": environment_id,
        "protocol": "fixed-checkpoint MiniGrid latent-prediction contact",
        "sample_counts": {
            "total": float(source.shape[0]),
            "train": float(source_train.shape[0]),
            "test": float(source_test.shape[0]),
        },
        "feature_dimension": float(source.shape[1]),
        "torch_environment": torch_environment or {},
        "dependency_status": dependency_status or {},
        "metrics": {
            "linear_aligned_r2": r2,
            "linear_aligned_mse": mse,
            "constant_baseline_mse": baseline_mse,
            "latent_prediction_score": latent_prediction_score,
            "mean_cosine_similarity": float(np.mean(cosine)),
            "flattened_correlation": _safe_corrcoef(aligned, source_test),
        },
        "claim_scope": (
            "same MiniGrid image/action stream as the BEDC native packet; V-JEPA2-AC encoder and "
            "action-conditioned predictor are loaded from the public Giant checkpoint; a linear "
            "alignment is fitted only on the train split for reporting latent-prediction contact"
        ),
        "cannot_claim": [
            "public benchmark superiority",
            "official V-JEPA2-AC benchmark reproduction",
            "end-to-end V-JEPA2-AC retraining",
            "certified operational claim without the separate LCCP artifact",
        ],
    }


def _encoder_features(
    carrier: dict[str, np.ndarray],
    *,
    batch_size: int,
    device: str,
    use_amp: bool,
) -> np.ndarray:
    import torch

    encoder, _, _ = _load_vjepa2_ac_giant_modules(num_frames=2)
    encoder.eval().to(device)
    videos = torch.from_numpy(carrier["videos"])
    features: list[np.ndarray] = []
    amp_enabled = bool(use_amp and device == "cuda")
    with torch.inference_mode():
        for start in range(0, videos.shape[0], batch_size):
            stop = min(start + batch_size, videos.shape[0])
            video = videos[start:stop].to(device, non_blocking=True)
            with torch.cuda.amp.autocast(enabled=amp_enabled):
                tokens = encoder(video)
                pooled = tokens.mean(dim=1)
            features.append(pooled.detach().float().cpu().numpy())
            del video, tokens, pooled
            if device == "cuda":
                torch.cuda.empty_cache()
    return np.concatenate(features, axis=0)


def run_vjepa2_ac_minigrid_latent_prediction(
    *,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
    sample_count: int = 96,
    train_count: int = 64,
    seed: int = 20260610,
    batch_size: int = 1,
    device: str = "cuda",
    use_amp: bool = True,
) -> dict[str, Any]:
    deps = _dependency_status()
    cuda = _cuda_environment_report()
    if device == "cuda" and not cuda.get("cuda_available"):
        return {
            "schema_id": "bedc-vjepa2-ac-minigrid-latent-prediction",
            "status": "unavailable",
            "candidate_id": "vjepa2-ac-vit-giant",
            "environment_id": environment_id,
            "dependency_status": deps,
            "torch_environment": cuda,
            "reason": "CUDA was requested but torch.cuda.is_available() is false",
            "cannot_claim": [
                "V-JEPA2-AC MiniGrid latent-prediction contact",
                "public benchmark superiority",
            ],
        }
    try:
        carrier = _collect_minigrid_transitions(
            environment_id=environment_id,
            sample_count=sample_count,
            seed=seed,
        )
        predicted = _extract_features(
            carrier,
            batch_size=batch_size,
            device=device,
            use_amp=use_amp,
        )
        source = _encoder_features(
            carrier,
            batch_size=batch_size,
            device=device,
            use_amp=use_amp,
        )
        return build_vjepa2_ac_latent_prediction_packet(
            source_features=source,
            predicted_features=predicted,
            train_count=train_count,
            environment_id=environment_id,
            torch_environment=cuda,
            dependency_status=deps,
        )
    except Exception as exc:  # pragma: no cover - environment-dependent checkpoint path
        return {
            "schema_id": "bedc-vjepa2-ac-minigrid-latent-prediction",
            "status": "unavailable",
            "candidate_id": "vjepa2-ac-vit-giant",
            "environment_id": environment_id,
            "dependency_status": deps,
            "torch_environment": cuda,
            "exception_type": type(exc).__name__,
            "message": str(exc),
            "trace_tail": traceback.format_exc().splitlines()[-8:],
            "cannot_claim": [
                "V-JEPA2-AC MiniGrid latent-prediction contact",
                "public benchmark superiority",
            ],
        }


def write_vjepa2_ac_minigrid_latent_prediction(path: str | Path) -> dict[str, Any]:
    packet = run_vjepa2_ac_minigrid_latent_prediction()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet
