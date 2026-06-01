import math

import pytest

from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from scripts import run_gaussian_ou_lejepa
from scripts import run_gaussian_ou_sweep as sweep


def make_envelope(*, classifier_name="standardized-nonlinear-observation", metric_base=1.0):
    metrics = {
        name: float(metric_base + index)
        for index, name in enumerate(sweep.METRIC_NAMES)
    }
    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id="fixture-run",
        source_spec={
            "name": "gaussian-ou-toy-world",
            "latent_dim": 2,
            "sample_count": 8,
            "rho": 0.3,
            "mixing": "sinusoidal-parabolic-shear",
        },
        pattern_spec={"name": "latent-linear-recovery"},
        classifier_spec={
            "name": classifier_name,
            "output_dim": 2,
            "training": "fixture-training",
        },
        stability_spec={
            "name": "fixed-seed-single-source",
            "seed": 101,
            "pair_process": "ornstein-uhlenbeck",
        },
        metrics=metrics,
        ledger_gaps=["kind=fixture; residue=gap; severity=none; status=closed"],
        debt_items=["kind=fixture; residue=debt; severity=none; status=closed; score=0.000000"],
        artifacts={
            "envelope": "reports/fixture_envelope.json",
            "report": "reports/fixture_report.md",
        },
        bedc_refs=["papers/bedc/preamble.tex:closurestatus"],
    )


def test_derive_seeds_uses_deterministic_quadratic_spacing():
    assert sweep._derive_seeds(430, 5) == [430, 1476, 2596, 3790, 5058]
    assert sweep._derive_seeds(17, 0) == []


def test_run_record_passes_sweep_arguments_and_records_ok_status(monkeypatch):
    calls = []

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return make_envelope(
            classifier_name=sweep.TORCH_CLASSIFIER if kwargs["use_torch"] else "fallback-fixture",
            metric_base=2.0,
        )

    monkeypatch.setattr(sweep, "run_experiment", fake_run_experiment)

    fallback = sweep._run_record(arm="fallback", seed=1476, rho=0.6, sample_count=12)
    torch = sweep._run_record(arm="torch", seed=2596, rho=0.82, sample_count=16)

    assert fallback["status"] == "ok"
    assert fallback["classifier_name"] == "fallback-fixture"
    assert fallback["metrics"]["quality_q"] == pytest.approx(9.0)
    assert fallback["envelope"]["classifier_spec"]["name"] == "fallback-fixture"

    assert torch["status"] == "ok"
    assert torch["classifier_name"] == sweep.TORCH_CLASSIFIER
    assert torch["metrics"]["quality_margin"] == pytest.approx(11.0)

    assert calls == [
        {
            "use_torch": False,
            "sample_count": 12,
            "seed": 1476,
            "rho": 0.6,
            "run_id": "gaussian-ou-lejepa-fallback-seed-1476-rho-0p6",
            "envelope_artifact": "reports/gaussian_ou_sweep.json",
            "report_artifact": "reports/gaussian_ou_sweep_report.md",
        },
        {
            "use_torch": True,
            "sample_count": 16,
            "seed": 2596,
            "rho": 0.82,
            "run_id": "gaussian-ou-lejepa-torch-seed-2596-rho-0p82",
            "envelope_artifact": "reports/gaussian_ou_sweep.json",
            "report_artifact": "reports/gaussian_ou_sweep_report.md",
        },
    ]


def test_run_record_marks_torch_fallback_as_skipped(monkeypatch):
    def fake_run_experiment(**kwargs):
        assert kwargs["use_torch"] is True
        return make_envelope(classifier_name="standardized-nonlinear-observation")

    monkeypatch.setattr(sweep, "run_experiment", fake_run_experiment)

    record = sweep._run_record(arm="torch", seed=3790, rho=0.95, sample_count=20)

    assert record == {
        "arm": "torch",
        "rho": 0.95,
        "seed": 3790,
        "sample_count": 20,
        "status": "skipped",
        "skip_reason": "torch encoder unavailable; fallback result excluded from torch arm",
        "fallback_classifier_name": "standardized-nonlinear-observation",
    }


def test_aggregate_counts_metrics_and_torch_skip_rows():
    records = []
    for seed, value in ((430, 1.0), (1476, 3.0)):
        records.append(
            {
                "arm": "fallback",
                "rho": 0.3,
                "seed": seed,
                "status": "ok",
                "metrics": {name: value for name in sweep.METRIC_NAMES},
            }
        )
    records.append(
        {
            "arm": "torch",
            "rho": 0.3,
            "seed": 430,
            "status": "skipped",
            "skip_reason": "torch encoder unavailable; fallback result excluded from torch arm",
        }
    )

    aggregate = sweep._aggregate(records)
    fallback = aggregate["rho_0p3"]["fallback"]
    torch = aggregate["rho_0p3"]["torch"]
    metric = fallback["metrics"]["quality_q"]

    assert fallback["status"] == "ok"
    assert fallback["ok_count"] == 2
    assert fallback["skipped_count"] == 0
    assert fallback["seeds"] == [430, 1476]
    assert metric["n"] == 2
    assert metric["mean"] == pytest.approx(2.0)
    assert metric["std"] == pytest.approx(math.sqrt(2.0))
    assert metric["ci95"] == pytest.approx(1.96)

    assert torch["status"] == "skipped"
    assert torch["ok_count"] == 0
    assert torch["skipped_count"] == 1
    assert torch["skipped_seeds"] == [430]
    assert math.isnan(torch["metrics"]["quality_q"]["mean"])


def test_render_markdown_includes_skipped_record_rows():
    records = [
        {
            "arm": "fallback",
            "rho": 0.3,
            "seed": 430,
            "status": "ok",
            "metrics": {name: 1.0 for name in sweep.METRIC_NAMES},
        },
        {
            "arm": "torch",
            "rho": 0.3,
            "seed": 430,
            "status": "skipped",
            "skip_reason": "torch encoder unavailable; fallback result excluded from torch arm",
        },
    ]
    payload = {
        "generated_at": "2026-06-01T00:00:00+00:00",
        "config": {
            "seed_base": sweep.SEED_BASE,
            "seed_count": 1,
            "seeds": [430],
            "rho_values": list(sweep.RHO_VALUES),
            "arms": list(sweep.ARMS),
            "sample_count": 8,
        },
        "records": records,
        "aggregates": sweep._aggregate(records),
    }

    report = sweep._render_markdown(payload)

    assert "## Skipped records" in report
    assert "| rho | arm | seed | reason |" in report
    assert (
        "| 0.3 | torch | 430 | torch encoder unavailable; "
        "fallback result excluded from torch arm |"
    ) in report
    assert "| 0.3 | torch | skipped | `430` |" in report


def test_lejepa_experiment_propagates_custom_seed_and_rho():
    envelope = run_gaussian_ou_lejepa.run_experiment(
        use_torch=False,
        sample_count=64,
        seed=987,
        rho=0.41,
        run_id="custom-gaussian-ou",
        envelope_artifact="reports/custom_envelope.json",
        report_artifact="reports/custom_report.md",
    )

    assert envelope.run_id == "custom-gaussian-ou"
    assert envelope.source_spec["sample_count"] == 64
    assert envelope.source_spec["rho"] == 0.41
    assert envelope.stability_spec["seed"] == 987
    assert envelope.artifacts == {
        "envelope": "reports/custom_envelope.json",
        "report": "reports/custom_report.md",
    }
