import importlib.util

import numpy as np
import pytest

from bedc_quality_lab.report import write_quality_report
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from scripts import run_gaussian_ou_lejepa as runner


def assert_common_experiment_envelope(envelope):
    assert envelope.schema_id == SCHEMA_ID
    assert envelope.run_id == "gaussian-ou-lejepa-seed-23"
    assert envelope.source_spec == {
        "name": "gaussian-ou-toy-world",
        "latent_dim": 2,
        "sample_count": 384,
        "rho": 0.82,
        "mixing": "sinusoidal-parabolic-shear",
    }
    assert envelope.pattern_spec == {
        "name": "latent-linear-recovery",
        "target": "recover z from representation h by linear least squares",
    }
    assert envelope.stability_spec == {
        "name": "fixed-seed-single-source",
        "seed": 23,
        "pair_process": "ornstein-uhlenbeck",
    }
    assert envelope.artifacts == {
        "envelope": "reports/example_envelope.json",
        "report": "reports/quality_report.md",
    }
    assert envelope.ledger_gaps == [
        "finite-sample-only",
        "single-mixing-family",
        "no-global-claim",
    ]
    assert set(envelope.metrics) == {
        "linear_identifiability_r2",
        "orthogonality_error",
        "covariance_deviation",
        "approx_identifiability_proxy",
    }


def assert_meaningful_metric_thresholds(envelope, *, max_covariance_deviation=0.35):
    assert envelope.metrics["linear_identifiability_r2"] > 0.85
    assert envelope.metrics["approx_identifiability_proxy"] > 0.70
    assert envelope.metrics["orthogonality_error"] < 0.30
    assert envelope.metrics["covariance_deviation"] < max_covariance_deviation


def assert_artifact_payloads_can_be_written(envelope, tmp_path):
    envelope_path = tmp_path / envelope.artifacts["envelope"]
    report_path = tmp_path / envelope.artifacts["report"]

    envelope.write_json(envelope_path)
    write_quality_report(envelope, report_path)

    assert envelope_path.is_file()
    assert report_path.is_file()
    assert QualityEvidenceEnvelope.read_json(envelope_path) == envelope
    assert "gaussian-ou-lejepa-seed-23" in report_path.read_text(encoding="utf-8")


def test_experiment_fallback_has_stable_quality_envelope(tmp_path):
    envelope = runner.run_experiment(use_torch=False)

    assert_common_experiment_envelope(envelope)
    assert envelope.classifier_spec == {
        "name": "standardized-nonlinear-observation",
        "output_dim": 2,
        "training": "deterministic-standardization",
    }
    assert_meaningful_metric_thresholds(envelope)
    assert_artifact_payloads_can_be_written(envelope, tmp_path)


def test_experiment_torch_success_path_uses_tiny_encoder_metadata(monkeypatch):
    def fake_torch_encoder(x, x_pair, *, seed):
        assert x.shape == x_pair.shape == (384, 2)
        assert seed == 23
        return np.asarray(x, dtype=np.float64)

    monkeypatch.setattr(runner, "_torch_encoder", fake_torch_encoder)

    envelope = runner.run_experiment(use_torch=True)

    assert_common_experiment_envelope(envelope)
    assert envelope.classifier_spec == {
        "name": "tiny-mlp-2-128-128-2",
        "output_dim": 2,
        "training": "align-cov-mean",
    }
    assert_meaningful_metric_thresholds(envelope)


def test_experiment_torch_failure_silently_uses_fallback_metadata(monkeypatch):
    def failing_torch_encoder(x, x_pair, *, seed):
        raise RuntimeError("forced test failure")

    monkeypatch.setattr(runner, "_torch_encoder", failing_torch_encoder)

    envelope = runner.run_experiment(use_torch=True)

    assert_common_experiment_envelope(envelope)
    assert envelope.classifier_spec == {
        "name": "standardized-nonlinear-observation",
        "output_dim": 2,
        "training": "deterministic-standardization",
    }
    assert_meaningful_metric_thresholds(envelope)


def test_smoke_experiment_skips_without_torch():
    if importlib.util.find_spec("torch") is None:
        pytest.skip("torch is not installed")

    envelope = runner.run_experiment(use_torch=True)

    assert_common_experiment_envelope(envelope)
    assert envelope.classifier_spec["name"] in {
        "tiny-mlp-2-128-128-2",
        "standardized-nonlinear-observation",
    }
    assert envelope.classifier_spec["training"] in {
        "align-cov-mean",
        "deterministic-standardization",
    }
    assert envelope.classifier_spec["output_dim"] == 2
    assert_meaningful_metric_thresholds(envelope, max_covariance_deviation=0.60)
