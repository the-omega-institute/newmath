"""Optional torch helpers for the tiny Gaussian-OU encoder."""

from __future__ import annotations

import random
from typing import Any

import numpy as np


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


def choose_device() -> str:
    torch = require_torch()
    if hasattr(torch.backends, "mps") and torch.backends.mps.is_available():
        return "mps"
    return "cpu"


def build_tiny_encoder() -> Any:
    torch = require_torch()
    return torch.nn.Sequential(
        torch.nn.Linear(2, 128),
        torch.nn.GELU(),
        torch.nn.Linear(128, 128),
        torch.nn.GELU(),
        torch.nn.Linear(128, 2),
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
