import importlib.util

import pytest


def test_smoke_experiment_skips_without_torch():
    if importlib.util.find_spec("torch") is None:
        pytest.skip("torch is not installed")

    from scripts.run_gaussian_ou_lejepa import run_experiment

    envelope = run_experiment(use_torch=True)
    assert envelope.metrics["linear_identifiability_r2"] >= 0.0
    assert envelope.metrics["approx_identifiability_proxy"] >= 0.0
    assert envelope.artifacts["envelope"] == "reports/example_envelope.json"
