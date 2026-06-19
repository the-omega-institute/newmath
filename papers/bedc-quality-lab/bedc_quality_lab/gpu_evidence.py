"""GPU provenance helpers for BEDC quality-lab reports."""

from __future__ import annotations

import subprocess
from collections.abc import Callable, Sequence
from typing import Any

from bedc_quality_lab.model import choose_device, require_torch


Runner = Callable[..., subprocess.CompletedProcess[str]]


def _run_nvidia_smi(runner: Runner) -> dict[str, Any]:
    command = [
        "nvidia-smi",
        "--query-gpu=name,driver_version,memory.total",
        "--format=csv,noheader",
    ]
    try:
        result = runner(command, check=False, capture_output=True, text=True, timeout=10)
    except (FileNotFoundError, subprocess.SubprocessError, OSError) as exc:
        return {
            "available": False,
            "command": " ".join(command),
            "returncode": None,
            "stdout": "",
            "stderr": str(exc),
            "gpus": [],
        }
    stdout = str(result.stdout or "").strip()
    stderr = str(result.stderr or "").strip()
    gpus = []
    if result.returncode == 0 and stdout:
        for line in stdout.splitlines():
            parts = [part.strip() for part in line.split(",")]
            if len(parts) >= 3:
                gpus.append(
                    {
                        "name": parts[0],
                        "driver_version": parts[1],
                        "memory_total": parts[2],
                    }
                )
    return {
        "available": bool(result.returncode == 0 and gpus),
        "command": " ".join(command),
        "returncode": int(result.returncode),
        "stdout": stdout,
        "stderr": stderr,
        "gpus": gpus,
    }


def collect_gpu_evidence(
    *,
    requested_device: str = "cuda",
    runner: Runner = subprocess.run,
) -> dict[str, Any]:
    torch = require_torch()
    device_resolution: dict[str, Any]
    try:
        device_resolution = choose_device(requested_device).to_dict()
    except RuntimeError as exc:
        device_resolution = {
            "requested_device": requested_device,
            "resolved_device": "",
            "resolution_status": "unavailable",
            "resolution_reason": str(exc),
            "backend_details": {
                "torch": str(getattr(torch, "__version__", "unknown")),
                "cuda_available": bool(torch.cuda.is_available()),
                "mps_available": False,
            },
        }
    cuda_available = bool(torch.cuda.is_available())
    cuda_device_name = str(torch.cuda.get_device_name(0)) if cuda_available else ""
    return {
        "schema_id": "bedc-gpu-evidence",
        "torch": {
            "version": str(getattr(torch, "__version__", "unknown")),
            "cuda_available": cuda_available,
            "cuda_device_count": int(torch.cuda.device_count()) if cuda_available else 0,
            "cuda_device_name": cuda_device_name,
            "device_resolution": device_resolution,
        },
        "nvidia_smi": _run_nvidia_smi(runner),
    }


def gpu_evidence_passes(evidence: dict[str, Any], *, required_device: str = "cuda") -> bool:
    torch_info = evidence.get("torch", {})
    resolution = torch_info.get("device_resolution", {})
    return bool(
        required_device == "cuda"
        and torch_info.get("cuda_available") is True
        and resolution.get("resolved_device") == "cuda"
        and evidence.get("nvidia_smi", {}).get("available") is True
    )


def compact_gpu_names(evidence: dict[str, Any]) -> Sequence[str]:
    gpus = evidence.get("nvidia_smi", {}).get("gpus", [])
    if not isinstance(gpus, list):
        return []
    return [str(gpu.get("name", "")) for gpu in gpus if isinstance(gpu, dict) and gpu.get("name")]
