import types

import pytest

from bedc_quality_lab import model


class _Backend:
    def __init__(self, available):
        self._available = available

    def is_available(self):
        return self._available


def _torch_stub(*, cuda=False, mps=False):
    return types.SimpleNamespace(
        __version__="fixture-torch",
        cuda=types.SimpleNamespace(is_available=lambda: cuda),
        backends=types.SimpleNamespace(mps=_Backend(mps)),
    )


def test_choose_device_explicit_unavailable_mps_fails_closed(monkeypatch):
    monkeypatch.setattr(model, "require_torch", lambda: _torch_stub(cuda=False, mps=False))

    with pytest.raises(RuntimeError, match="mps device is not available"):
        model.choose_device("mps")


def test_choose_device_explicit_unavailable_cuda_fails_closed(monkeypatch):
    monkeypatch.setattr(model, "require_torch", lambda: _torch_stub(cuda=False, mps=True))

    with pytest.raises(RuntimeError, match="cuda device is not available"):
        model.choose_device("cuda")


def test_choose_device_auto_cpu_fallback_records_policy(monkeypatch):
    monkeypatch.setattr(model, "require_torch", lambda: _torch_stub(cuda=False, mps=False))

    resolution = model.choose_device("auto")

    assert str(resolution) == "cpu"
    assert resolution.to_dict() == {
        "requested_device": "auto",
        "resolved_device": "cpu",
        "resolution_status": "fallback",
        "resolution_reason": "auto-cpu-fallback-no-accelerator",
        "backend_details": {
            "torch": "fixture-torch",
            "cuda_available": False,
            "mps_available": False,
        },
    }


def test_choose_device_available_accelerator_records_backend_details(monkeypatch):
    monkeypatch.setattr(model, "require_torch", lambda: _torch_stub(cuda=False, mps=True))

    resolution = model.choose_device("mps")

    assert resolution.requested_device == "mps"
    assert resolution.resolved_device == "mps"
    assert resolution.resolution_status == "available"
    assert resolution.backend_details["mps_available"] is True
