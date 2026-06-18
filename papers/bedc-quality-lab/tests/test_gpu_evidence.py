from __future__ import annotations

import subprocess
from dataclasses import dataclass

from bedc_quality_lab import gpu_evidence


class _FakeCuda:
    def is_available(self) -> bool:
        return True

    def device_count(self) -> int:
        return 1

    def get_device_name(self, index: int) -> str:
        assert index == 0
        return "Test CUDA"


class _FakeTorch:
    __version__ = "2.test"
    cuda = _FakeCuda()


@dataclass(frozen=True)
class _Resolution:
    requested_device: str
    resolved_device: str

    def to_dict(self) -> dict[str, object]:
        return {
            "requested_device": self.requested_device,
            "resolved_device": self.resolved_device,
            "resolution_status": "available",
            "resolution_reason": "test",
            "backend_details": {"torch": "2.test", "cuda_available": True, "mps_available": False},
        }


def test_collect_gpu_evidence_records_torch_cuda_and_nvidia_smi(monkeypatch):
    monkeypatch.setattr(gpu_evidence, "require_torch", lambda: _FakeTorch())
    monkeypatch.setattr(gpu_evidence, "choose_device", lambda requested: _Resolution(requested, "cuda"))

    def runner(command, **kwargs):
        assert command[0] == "nvidia-smi"
        assert kwargs["capture_output"] is True
        return subprocess.CompletedProcess(
            command,
            0,
            stdout="Test CUDA, 555.12, 8192 MiB\n",
            stderr="",
        )

    evidence = gpu_evidence.collect_gpu_evidence(requested_device="cuda", runner=runner)

    assert evidence["torch"]["cuda_available"] is True
    assert evidence["torch"]["cuda_device_name"] == "Test CUDA"
    assert evidence["nvidia_smi"]["available"] is True
    assert evidence["nvidia_smi"]["gpus"][0]["driver_version"] == "555.12"
    assert gpu_evidence.gpu_evidence_passes(evidence)
    assert gpu_evidence.compact_gpu_names(evidence) == ["Test CUDA"]


def test_collect_gpu_evidence_fails_closed_when_nvidia_smi_is_missing(monkeypatch):
    monkeypatch.setattr(gpu_evidence, "require_torch", lambda: _FakeTorch())
    monkeypatch.setattr(gpu_evidence, "choose_device", lambda requested: _Resolution(requested, "cuda"))

    def runner(command, **kwargs):
        raise FileNotFoundError("nvidia-smi")

    evidence = gpu_evidence.collect_gpu_evidence(requested_device="cuda", runner=runner)

    assert evidence["torch"]["cuda_available"] is True
    assert evidence["nvidia_smi"]["available"] is False
    assert gpu_evidence.gpu_evidence_passes(evidence) is False
