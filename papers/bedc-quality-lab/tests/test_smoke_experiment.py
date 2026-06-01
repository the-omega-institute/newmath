import importlib.util
from dataclasses import replace
from pathlib import Path

import numpy as np
import pytest

from bedc_quality_lab.report import write_quality_report
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from scripts import run_gaussian_ou_lejepa as runner
from scripts import run_quality_improvement as improvement


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
    assert envelope.ledger_gaps
    assert envelope.debt_items
    assert all(row.startswith("kind=") for row in envelope.ledger_gaps)
    assert all("; residue=" in row for row in envelope.ledger_gaps)
    assert all("kind=" in row and "score=" in row for row in envelope.debt_items)
    assert set(envelope.metrics) == {
        "linear_identifiability_r2",
        "orthogonality_error",
        "covariance_deviation",
        "approx_identifiability_proxy",
        "alignment_loss",
        "alignment_gap_delta",
        "whitening_deviation_epsilon",
        "normalized_gap_d",
        "theorem3_bound",
        "actual_recovery_error",
        "bound_margin",
        "quality_benefit",
        "quality_cost",
        "quality_debt",
        "quality_q",
        "quality_threshold",
        "quality_margin",
    }


FALLBACK_LEDGER_GAPS = [
    "kind=classifier; residue=optimizer-certificate; severity=medium; status=partial",
    "kind=source; residue=finite-sample-support; severity=high; status=open",
    "kind=source; residue=mixing-family-coverage; severity=high; status=open",
    "kind=source; residue=source-coverage; severity=high; status=open",
    "kind=verification; residue=identifiability-proxy-margin; severity=medium; status=partial",
]

FALLBACK_DEBT_ITEMS = [
    "kind=source; residue=source-coverage; severity=high; status=open; score=0.180000",
    "kind=source; residue=mixing-family-coverage; severity=high; status=open; score=0.220000",
    "kind=source; residue=finite-sample-support; severity=high; status=open; score=0.200000",
    "kind=classifier; residue=optimizer-certificate; severity=medium; status=partial; score=0.100000",
    "kind=generalization; residue=global-claim-boundary; severity=none; status=closed; score=0.000000",
]

TORCH_METADATA_LEDGER_GAPS = [
    "kind=classifier; residue=optimizer-certificate; severity=high; status=open",
    "kind=source; residue=finite-sample-support; severity=high; status=open",
    "kind=source; residue=mixing-family-coverage; severity=high; status=open",
    "kind=source; residue=source-coverage; severity=high; status=open",
    "kind=verification; residue=identifiability-proxy-margin; severity=medium; status=partial",
]

TORCH_METADATA_DEBT_ITEMS = [
    "kind=source; residue=source-coverage; severity=high; status=open; score=0.180000",
    "kind=source; residue=mixing-family-coverage; severity=high; status=open; score=0.220000",
    "kind=source; residue=finite-sample-support; severity=high; status=open; score=0.200000",
    "kind=classifier; residue=optimizer-certificate; severity=high; status=open; score=0.200000",
    "kind=generalization; residue=global-claim-boundary; severity=none; status=closed; score=0.000000",
]


def assert_classifier_spec_base(envelope, expected):
    for key, value in expected.items():
        assert envelope.classifier_spec[key] == value


def assert_classifier_certificate(envelope):
    classifier_spec = envelope.classifier_spec

    assert classifier_spec["cert_method"] == "inline-threshold"
    assert classifier_spec["cert_status"] == "certified"
    assert isinstance(classifier_spec["cert_score"], (int, float))
    assert isinstance(classifier_spec["cert_r2"], (int, float))
    assert isinstance(classifier_spec["cert_proxy"], (int, float))
    assert isinstance(classifier_spec["cert_reason"], str)
    assert classifier_spec["cert_threshold"] == {
        "linear_identifiability_r2": 0.85,
        "approx_identifiability_proxy": 0.70,
    }
    assert np.isclose(
        classifier_spec["cert_r2"],
        envelope.metrics["linear_identifiability_r2"],
    )
    assert np.isclose(
        classifier_spec["cert_proxy"],
        envelope.metrics["approx_identifiability_proxy"],
    )
    assert classifier_spec["split_policy"] == "train-eval-disjoint"
    assert classifier_spec["train_fraction"] == 0.70
    assert classifier_spec["train_count"] == round(0.70 * envelope.source_spec["sample_count"])
    assert classifier_spec["eval_count"] == envelope.source_spec["sample_count"] - classifier_spec["train_count"]
    assert classifier_spec["overlap_count"] == 0
    assert isinstance(classifier_spec["train_index_checksum"], int)
    assert isinstance(classifier_spec["eval_index_checksum"], int)


def assert_canonical_quality_rows(envelope, *, ledger_gaps, debt_items):
    assert envelope.ledger_gaps == ledger_gaps
    assert envelope.debt_items == debt_items


def assert_meaningful_metric_thresholds(
    envelope,
    *,
    max_orthogonality_error=0.53,
    max_covariance_deviation=0.63,
):
    assert envelope.metrics["linear_identifiability_r2"] > 0.85
    assert envelope.metrics["approx_identifiability_proxy"] > 0.70
    assert envelope.metrics["orthogonality_error"] < max_orthogonality_error
    assert envelope.metrics["covariance_deviation"] < max_covariance_deviation
    assert envelope.metrics["alignment_loss"] >= 0.0
    assert envelope.metrics["alignment_gap_delta"] >= 0.0
    assert envelope.metrics["whitening_deviation_epsilon"] >= 0.0
    assert envelope.metrics["normalized_gap_d"] >= 0.0
    assert envelope.metrics["theorem3_bound"] >= 0.0
    assert np.isfinite(envelope.metrics["actual_recovery_error"])
    assert envelope.metrics["bound_margin"] == pytest.approx(
        envelope.metrics["theorem3_bound"] - envelope.metrics["actual_recovery_error"]
    )


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
    assert_classifier_spec_base(
        envelope,
        {
            "name": "standardized-nonlinear-observation",
            "output_dim": 2,
            "training": "deterministic-standardization",
        },
    )
    assert_classifier_certificate(envelope)
    assert_canonical_quality_rows(
        envelope,
        ledger_gaps=FALLBACK_LEDGER_GAPS,
        debt_items=FALLBACK_DEBT_ITEMS,
    )
    assert_meaningful_metric_thresholds(envelope)
    assert_artifact_payloads_can_be_written(envelope, tmp_path)


def test_parameterized_experiment_preserves_producer_chain():
    envelope = runner.run_experiment(
        use_torch=False,
        sample_count=2048,
        run_id="gaussian-ou-lejepa-finite-sample-after",
        envelope_artifact="reports/improvement_after_envelope.json",
        report_artifact="reports/quality_improvement_report.md",
    )

    assert envelope.schema_id == SCHEMA_ID
    assert envelope.run_id == "gaussian-ou-lejepa-finite-sample-after"
    assert envelope.source_spec == {
        "name": "gaussian-ou-toy-world",
        "latent_dim": 2,
        "sample_count": 2048,
        "rho": 0.82,
        "mixing": "sinusoidal-parabolic-shear",
    }
    assert envelope.pattern_spec == {
        "name": "latent-linear-recovery",
        "target": "recover z from representation h by linear least squares",
    }
    assert_classifier_spec_base(
        envelope,
        {
            "name": "standardized-nonlinear-observation",
            "output_dim": 2,
            "training": "deterministic-standardization",
        },
    )
    assert_classifier_certificate(envelope)
    assert envelope.stability_spec == {
        "name": "fixed-seed-single-source",
        "seed": 23,
        "pair_process": "ornstein-uhlenbeck",
    }
    assert envelope.artifacts == {
        "envelope": "reports/improvement_after_envelope.json",
        "report": "reports/quality_improvement_report.md",
    }
    assert "kind=source; residue=finite-sample-support; severity=none; status=closed; score=0.000000" in envelope.debt_items
    assert all("kind=" in row and "score=" in row for row in envelope.debt_items)
    assert all(row.startswith("kind=") for row in envelope.ledger_gaps)
    assert all("; residue=" in row for row in envelope.ledger_gaps)


def test_improvement_projection_fails_closed_for_missing_or_malformed_target_row():
    envelope = runner.run_experiment(use_torch=False)
    missing = replace(
        envelope,
        debt_items=[row for row in envelope.debt_items if "residue=finite-sample-support;" not in row],
    )
    malformed = replace(
        envelope,
        debt_items=[
            "kind=source; residue=finite-sample-support; severity=high; status=open"
            if "residue=finite-sample-support;" in row
            else row
            for row in envelope.debt_items
        ],
    )

    with pytest.raises(ValueError):
        improvement._target_debt_row(missing)
    with pytest.raises(ValueError):
        improvement._target_debt_row(malformed)


def test_quality_improvement_delta_and_report_projection():
    before = runner.run_experiment(
        use_torch=False,
        sample_count=384,
        run_id="gaussian-ou-lejepa-finite-sample-before",
        envelope_artifact="reports/improvement_before_envelope.json",
        report_artifact="reports/quality_improvement_report.md",
    )
    after = runner.run_experiment(
        use_torch=False,
        sample_count=2048,
        run_id="gaussian-ou-lejepa-finite-sample-after",
        envelope_artifact="reports/improvement_after_envelope.json",
        report_artifact="reports/quality_improvement_report.md",
    )

    before_row = improvement._target_debt_row(before)
    after_row = improvement._target_debt_row(after)
    delta = improvement.quality_delta(before, after)
    report = improvement._render_improvement_report(before, after)

    assert before_row["status"] == "open"
    assert before_row["score"] == "0.200000"
    assert after_row["status"] == "closed"
    assert after_row["score"] == "0.000000"
    assert after.metrics["quality_q"] - before.metrics["quality_q"] > 0
    assert after.metrics["quality_debt"] - before.metrics["quality_debt"] < 0
    assert float(after_row["score"]) - float(before_row["score"]) < 0
    assert delta["target_residue"] == "finite-sample-support"
    assert delta["delta_q"] > 0
    assert delta["delta_debt"] < 0
    assert "reports/improvement_before_envelope.json" in report
    assert "reports/improvement_after_envelope.json" in report
    assert "delta_q" in report
    assert "delta_debt" in report
    assert "干预前 status：`open`" in report
    assert "干预后 status：`closed`" in report
    assert "目标 debt residue：`finite-sample-support`" in report


def test_experiment_torch_success_path_uses_tiny_encoder_metadata(monkeypatch):
    def fake_torch_encoder(train_x, train_x_pair, eval_x, eval_x_pair, *, seed):
        assert train_x.shape == train_x_pair.shape == (269, 2)
        assert eval_x.shape == eval_x_pair.shape == (115, 2)
        assert seed == 23
        h, h_pair = runner._fallback_encoder(train_x, eval_x, eval_x_pair)
        return h, h_pair

    monkeypatch.setattr(runner, "_torch_encoder", fake_torch_encoder)

    envelope = runner.run_experiment(use_torch=True)

    assert_common_experiment_envelope(envelope)
    assert_classifier_spec_base(
        envelope,
        {
            "name": "tiny-mlp-2-128-128-2",
            "output_dim": 2,
            "training": "align-cov-mean",
        },
    )
    assert_classifier_certificate(envelope)
    assert_canonical_quality_rows(
        envelope,
        ledger_gaps=TORCH_METADATA_LEDGER_GAPS,
        debt_items=TORCH_METADATA_DEBT_ITEMS,
    )
    assert_meaningful_metric_thresholds(envelope)


def test_experiment_torch_failure_silently_uses_fallback_metadata(monkeypatch):
    def failing_torch_encoder(train_x, train_x_pair, eval_x, eval_x_pair, *, seed):
        raise RuntimeError("forced test failure")

    monkeypatch.setattr(runner, "_torch_encoder", failing_torch_encoder)

    envelope = runner.run_experiment(use_torch=True)

    assert_common_experiment_envelope(envelope)
    assert_classifier_spec_base(
        envelope,
        {
            "name": "standardized-nonlinear-observation",
            "output_dim": 2,
            "training": "deterministic-standardization",
        },
    )
    assert_classifier_certificate(envelope)
    assert_canonical_quality_rows(
        envelope,
        ledger_gaps=FALLBACK_LEDGER_GAPS,
        debt_items=FALLBACK_DEBT_ITEMS,
    )
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
    assert_classifier_certificate(envelope)
    assert_meaningful_metric_thresholds(envelope, max_covariance_deviation=0.69)


def test_runner_uses_canonical_debt_and_ledger_producers():
    source = Path(runner.__file__).read_text(encoding="utf-8")

    assert "format_debt_items" in source
    assert "format_ledger_gaps" in source
    assert "finite-sample-only" not in source
    assert "single-mixing-family" not in source
    assert "no-global-claim" not in source
    assert "distribution-debt:" not in source


def test_train_eval_split_is_disjoint_and_deterministic():
    left_train, left_eval = runner._train_eval_split(384, seed=23)
    right_train, right_eval = runner._train_eval_split(384, seed=23)
    other_train, other_eval = runner._train_eval_split(384, seed=24)

    assert np.array_equal(left_train, right_train)
    assert np.array_equal(left_eval, right_eval)
    assert left_train.shape == (269,)
    assert left_eval.shape == (115,)
    assert np.intersect1d(left_train, left_eval).size == 0
    assert set(left_train.tolist()) | set(left_eval.tolist()) == set(range(384))
    assert not np.array_equal(left_train, other_train)
    assert not np.array_equal(left_eval, other_eval)


def test_fallback_standardizer_fits_train_only():
    train_x = np.array([[10.0, 100.0], [12.0, 104.0], [14.0, 108.0]], dtype=np.float64)
    eval_x = np.array([[12.0, 104.0]], dtype=np.float64)
    eval_x_pair = np.array([[16.0, 112.0]], dtype=np.float64)

    h, h_pair = runner._fallback_encoder(train_x, eval_x, eval_x_pair)

    assert h == pytest.approx(np.array([[0.0, 0.0]]))
    assert h_pair == pytest.approx(np.array([[2.44948974, 2.44948974]]))


def test_torch_encoder_receives_train_arrays_and_returns_eval_arrays(monkeypatch):
    calls = {}

    def fake_torch_encoder(train_x, train_x_pair, eval_x, eval_x_pair, *, seed):
        calls["train_x"] = np.array(train_x, copy=True)
        calls["train_x_pair"] = np.array(train_x_pair, copy=True)
        calls["eval_x"] = np.array(eval_x, copy=True)
        calls["eval_x_pair"] = np.array(eval_x_pair, copy=True)
        return np.asarray(eval_x, dtype=np.float64), np.asarray(eval_x_pair, dtype=np.float64)

    monkeypatch.setattr(runner, "_torch_encoder", fake_torch_encoder)

    envelope = runner.run_experiment(use_torch=True)

    assert calls["train_x"].shape == calls["train_x_pair"].shape == (269, 2)
    assert calls["eval_x"].shape == calls["eval_x_pair"].shape == (115, 2)
    assert not any(np.array_equal(row, calls["eval_x"][0]) for row in calls["train_x"])
    assert envelope.classifier_spec["eval_count"] == 115


def test_report_includes_bound_metrics_without_positive_margin_assumption(tmp_path):
    envelope = runner.run_experiment(use_torch=False)
    report_path = tmp_path / "quality_report.md"

    write_quality_report(envelope, report_path)
    report = report_path.read_text(encoding="utf-8")

    assert "## Identifiability Bound" in report
    assert "`theorem3_bound`" in report
    assert "`bound_margin`" in report
    assert envelope.metrics["bound_margin"] == pytest.approx(
        envelope.metrics["theorem3_bound"] - envelope.metrics["actual_recovery_error"]
    )
