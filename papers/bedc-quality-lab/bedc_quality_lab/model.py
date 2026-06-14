"""Optional torch helpers for the tiny Gaussian-OU encoder."""

from __future__ import annotations

import os
import random
from dataclasses import asdict, dataclass
from typing import Any

import numpy as np

os.environ.setdefault("CUBLAS_WORKSPACE_CONFIG", ":4096:8")


def require_torch() -> Any:
    try:
        import torch
    except ImportError as exc:
        raise RuntimeError("torch is not installed") from exc
    return torch


def set_deterministic_seed(seed: int) -> None:
    random.seed(seed)
    np.random.seed(seed)
    try:
        torch = require_torch()
    except RuntimeError:
        return
    torch.manual_seed(seed)
    if hasattr(torch, "use_deterministic_algorithms"):
        try:
            torch.use_deterministic_algorithms(True, warn_only=True)
        except TypeError:
            torch.use_deterministic_algorithms(True)


@dataclass(frozen=True)
class DeviceResolution:
    requested_device: str
    resolved_device: str
    resolution_status: str
    resolution_reason: str
    backend_details: dict[str, Any]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def __str__(self) -> str:
        return self.resolved_device


def _torch_backend_details(torch: Any) -> dict[str, Any]:
    cuda_available = bool(hasattr(torch, "cuda") and torch.cuda.is_available())
    mps_backend = getattr(getattr(torch, "backends", None), "mps", None)
    mps_available = bool(mps_backend is not None and mps_backend.is_available())
    return {
        "torch": str(getattr(torch, "__version__", "unknown")),
        "cuda_available": cuda_available,
        "mps_available": mps_available,
    }


def choose_device(requested: str = "auto") -> DeviceResolution:
    requested_device = str(requested)
    if requested_device not in {"auto", "cpu", "mps", "cuda"}:
        raise ValueError(f"unsupported requested device: {requested_device}")
    torch = require_torch()
    backend_details = _torch_backend_details(torch)
    if requested_device == "cpu":
        return DeviceResolution(
            requested_device="cpu",
            resolved_device="cpu",
            resolution_status="available",
            resolution_reason="explicit-cpu",
            backend_details=backend_details,
        )
    if requested_device == "cuda":
        if backend_details["cuda_available"]:
            return DeviceResolution(
                requested_device="cuda",
                resolved_device="cuda",
                resolution_status="available",
                resolution_reason="explicit-cuda-available",
                backend_details=backend_details,
            )
        raise RuntimeError("requested cuda device is not available")
    if requested_device == "mps":
        if backend_details["mps_available"]:
            return DeviceResolution(
                requested_device="mps",
                resolved_device="mps",
                resolution_status="available",
                resolution_reason="explicit-mps-available",
                backend_details=backend_details,
            )
        raise RuntimeError("requested mps device is not available")
    if backend_details["cuda_available"]:
        return DeviceResolution(
            requested_device="auto",
            resolved_device="cuda",
            resolution_status="available",
            resolution_reason="auto-cuda-available",
            backend_details=backend_details,
        )
    if backend_details["mps_available"]:
        return DeviceResolution(
            requested_device="auto",
            resolved_device="mps",
            resolution_status="available",
            resolution_reason="auto-mps-available",
            backend_details=backend_details,
        )
    return DeviceResolution(
        requested_device="auto",
        resolved_device="cpu",
        resolution_status="fallback",
        resolution_reason="auto-cpu-fallback-no-accelerator",
        backend_details=backend_details,
    )


def build_tiny_encoder(output_dim: int = 2) -> Any:
    torch = require_torch()
    if not isinstance(output_dim, int) or output_dim < 1:
        raise ValueError("output_dim must be a positive integer")
    return torch.nn.Sequential(
        torch.nn.Linear(2, 128),
        torch.nn.GELU(),
        torch.nn.Linear(128, 128),
        torch.nn.GELU(),
        torch.nn.Linear(128, output_dim),
    )


def align_loss(h: Any, h_pair: Any) -> Any:
    return ((h - h_pair) ** 2).mean()


def covariance_loss(h: Any) -> Any:
    torch = require_torch()
    centered = h - h.mean(dim=0, keepdim=True)
    cov = centered.T @ centered / max(1, h.shape[0] - 1)
    eye = torch.eye(h.shape[1], device=h.device, dtype=h.dtype)
    return ((cov - eye) ** 2).mean()


def mean_loss(h: Any) -> Any:
    return (h.mean(dim=0) ** 2).mean()


def representation_loss(h: Any, h_pair: Any) -> Any:
    return align_loss(h, h_pair) + covariance_loss(h) + 0.1 * mean_loss(h)
