from __future__ import annotations

from types import SimpleNamespace

import pytest

from bedc_quality_lab import backends
from bedc_quality_lab.backends import sigreg
from bedc_quality_lab.backends.sigreg import SIGRegBackendEvidenceAdapter
from bedc_quality_lab.cost_protocol import SCOPED_DEBT_ROWS
from bedc_quality_lab.discovery_compiler.backend import BackendEvidenceAdapter, TheoryBackend
from bedc_quality_lab.discovery_compiler.compiler import load_adapter
from bedc_quality_lab.ledger import LedgerRowKey
from scripts import run_sigreg_training_proxy


EXPECTED_METRICS = (
    "covariance_proxy_current_alignment_mean",
    "covariance_proxy_current_sigreg_sliced_cf_mean",
    "covariance_proxy_current_loss_mean",
    "true_sigreg_sliced_cf_alignment_mean",
    "true_sigreg_sliced_cf_sigreg_sliced_cf_mean",
    "true_sigreg_sliced_cf_loss_mean",
    "vicreg_like_covariance_alignment_mean",
    "vicreg_like_covariance_sigreg_sliced_cf_mean",
    "vicreg_like_covariance_loss_mean",
    "alignment_only_alignment_mean",
    "alignment_only_sigreg_sliced_cf_mean",
    "alignment_only_loss_mean",
)
EXPECTED_LEDGER_ROWS = (
    "source/latent-distribution-gaussianity",
    "source/transition-isotropy",
    "source/dimension-match",
    "source/finite-sample-support",
    "classifier/optimizer-certificate",
    "generalization/global-claim-boundary",
)


def fake_sigreg_payload() -> dict:
    return {
        "run_id": "fake-sigreg-run",
        "source_artifacts": {
            "producer": "scripts/run_sigreg_training_proxy.py",
            "cost_protocol": "configs/default_cost_protocol.yaml",
        },
        "config": {
            "sample_count": 192,
            "steps": 28,
            "seeds": [17, 29, 41],
            "lambda_sigreg": 0.35,
            "directions": 16,
            "frequencies": [0.5, 1.0, 2.0],
            "learning_rate": 0.002,
            "rho": 0.82,
            "arms": [
                "covariance_proxy_current",
                "true_sigreg_sliced_cf",
                "vicreg_like_covariance",
                "alignment_only",
            ],
        },
        "arm_protocol": {
            "exact_arm_count": 4,
            "arms": [
                "covariance_proxy_current",
                "true_sigreg_sliced_cf",
                "vicreg_like_covariance",
                "alignment_only",
            ],
            "covariance_proxy_arm": "covariance_proxy_current",
            "sigreg_objective_arm": "true_sigreg_sliced_cf",
        },
        "arm_summaries": {
            "covariance_proxy_current": {
                "alignment_mean": 1.0,
                "sigreg_sliced_cf_mean": 2.0,
                "loss_mean": 3.0,
            },
            "true_sigreg_sliced_cf": {
                "alignment_mean": 4.0,
                "sigreg_sliced_cf_mean": 5.0,
                "loss_mean": 6.0,
            },
            "vicreg_like_covariance": {
                "alignment_mean": 7.0,
                "sigreg_sliced_cf_mean": 8.0,
                "loss_mean": 9.0,
            },
            "alignment_only": {
                "alignment_mean": 10.0,
                "sigreg_sliced_cf_mean": 11.0,
                "loss_mean": 12.0,
            },
        },
    }


def test_adapter_metadata_and_module_loading_contract():
    adapter: BackendEvidenceAdapter = SIGRegBackendEvidenceAdapter()
    backend = adapter.backend

    assert isinstance(backend, TheoryBackend)
    assert backend.name == "sigreg"
    assert backend.scope_kind == "non-canonical-backend-probe"
    assert "sigreg" in backends.__all__
    assert backends.SIGRegBackendEvidenceAdapter is SIGRegBackendEvidenceAdapter
    assert sigreg.SIGRegBackendEvidenceAdapter is SIGRegBackendEvidenceAdapter
    assert load_adapter("bedc_quality_lab.backends.sigreg:SIGRegBackendEvidenceAdapter").backend.name == "sigreg"
    assert backend.metrics == EXPECTED_METRICS
    assert tuple(f"{row['kind']}/{row['residue']}" for row in backend.ledger_rows) == EXPECTED_LEDGER_ROWS
    assert "canonical report production" in backend.not_claimed
    assert "terminal verdict classification" in backend.not_claimed
    assert "terminal_verdict" not in backend.metrics
    assert all("terminal_verdict" not in row for row in backend.ledger_rows)


def test_compute_metrics_delegates_to_sigreg_payload_builder_without_artifact_writes(monkeypatch, tmp_path):
    calls = []

    def fake_build_payload(**kwargs):
        calls.append(kwargs)
        return fake_sigreg_payload()

    def fail_write_artifacts(*args, **kwargs):
        raise AssertionError("adapter must not write canonical artifacts")

    monkeypatch.setattr(sigreg.run_sigreg_training_proxy, "build_payload", fake_build_payload)
    monkeypatch.setattr(sigreg.run_sigreg_training_proxy, "write_artifacts", fail_write_artifacts)

    payload = SIGRegBackendEvidenceAdapter().compute_metrics(root=tmp_path, generated_at="fake-time")

    assert calls == [
        {
            "run_id": "sigreg-backend-probe",
            "generated_at": "fake-time",
            "json_artifact": "reports/backend-probes/sigreg/evidence-envelope.json",
            "report_artifact": "reports/backend-probes/sigreg/quality-report.md",
        }
    ]
    assert not any(tmp_path.iterdir())
    assert payload["generated_at"] == "fake-time"
    assert tuple(payload["metrics"]) == EXPECTED_METRICS
    assert "claim_gate" not in payload
    assert "hardgate" not in payload
    assert "terminal_verdict" not in repr(payload)


def test_exact_flat_metric_contract_projects_only_from_arm_summaries(monkeypatch, tmp_path):
    monkeypatch.setattr(sigreg.run_sigreg_training_proxy, "build_payload", lambda **kwargs: fake_sigreg_payload())

    payload = SIGRegBackendEvidenceAdapter().compute_metrics(root=tmp_path)

    assert payload["metrics"] == {
        "covariance_proxy_current_alignment_mean": 1.0,
        "covariance_proxy_current_sigreg_sliced_cf_mean": 2.0,
        "covariance_proxy_current_loss_mean": 3.0,
        "true_sigreg_sliced_cf_alignment_mean": 4.0,
        "true_sigreg_sliced_cf_sigreg_sliced_cf_mean": 5.0,
        "true_sigreg_sliced_cf_loss_mean": 6.0,
        "vicreg_like_covariance_alignment_mean": 7.0,
        "vicreg_like_covariance_sigreg_sliced_cf_mean": 8.0,
        "vicreg_like_covariance_loss_mean": 9.0,
        "alignment_only_alignment_mean": 10.0,
        "alignment_only_sigreg_sliced_cf_mean": 11.0,
        "alignment_only_loss_mean": 12.0,
    }
    assert payload["metric_sources"] == {
        "covariance_proxy_current_alignment_mean": "$.arm_summaries.covariance_proxy_current.alignment_mean",
        "covariance_proxy_current_sigreg_sliced_cf_mean": "$.arm_summaries.covariance_proxy_current.sigreg_sliced_cf_mean",
        "covariance_proxy_current_loss_mean": "$.arm_summaries.covariance_proxy_current.loss_mean",
        "true_sigreg_sliced_cf_alignment_mean": "$.arm_summaries.true_sigreg_sliced_cf.alignment_mean",
        "true_sigreg_sliced_cf_sigreg_sliced_cf_mean": "$.arm_summaries.true_sigreg_sliced_cf.sigreg_sliced_cf_mean",
        "true_sigreg_sliced_cf_loss_mean": "$.arm_summaries.true_sigreg_sliced_cf.loss_mean",
        "vicreg_like_covariance_alignment_mean": "$.arm_summaries.vicreg_like_covariance.alignment_mean",
        "vicreg_like_covariance_sigreg_sliced_cf_mean": "$.arm_summaries.vicreg_like_covariance.sigreg_sliced_cf_mean",
        "vicreg_like_covariance_loss_mean": "$.arm_summaries.vicreg_like_covariance.loss_mean",
        "alignment_only_alignment_mean": "$.arm_summaries.alignment_only.alignment_mean",
        "alignment_only_sigreg_sliced_cf_mean": "$.arm_summaries.alignment_only.sigreg_sliced_cf_mean",
        "alignment_only_loss_mean": "$.arm_summaries.alignment_only.loss_mean",
    }


def test_flat_metric_paths_exist_in_real_sigreg_payload():
    payload = run_sigreg_training_proxy.build_payload(
        run_id="fixture",
        generated_at="fixture-time",
        sample_count=32,
        steps=1,
        seeds=(17,),
        directions=2,
        frequencies=(0.5,),
        use_torch=False,
    )

    projected = sigreg._project_metrics(payload)

    assert tuple(projected) == EXPECTED_METRICS
    for source_path in SIGRegBackendEvidenceAdapter().compute_metrics.__globals__["_METRIC_PROJECTIONS"]:
        metric_name, arm, field = source_path
        assert projected[metric_name] == pytest.approx(payload["arm_summaries"][arm][field])


def test_exact_six_row_ledger_contract():
    assert tuple(f"{row['kind']}/{row['residue']}" for row in SIGRegBackendEvidenceAdapter.backend.ledger_rows) == EXPECTED_LEDGER_ROWS


def test_ledger_projection_uses_assess_debt_and_derive_ledger_gaps(monkeypatch, tmp_path):
    monkeypatch.setattr(sigreg.run_sigreg_training_proxy, "build_payload", lambda **kwargs: fake_sigreg_payload())
    original_assess_debt = sigreg.assess_debt
    original_derive_ledger_gaps = sigreg.derive_ledger_gaps
    calls = {"assess": [], "gaps": []}

    def wrapped_assess_debt(*args, **kwargs):
        calls["assess"].append((args, kwargs))
        return original_assess_debt(*args, **kwargs)

    def wrapped_derive_ledger_gaps(*args, **kwargs):
        calls["gaps"].append((args, kwargs))
        return original_derive_ledger_gaps(*args, **kwargs)

    monkeypatch.setattr(sigreg, "assess_debt", wrapped_assess_debt)
    monkeypatch.setattr(sigreg, "derive_ledger_gaps", wrapped_derive_ledger_gaps)

    rows = SIGRegBackendEvidenceAdapter().derive_ledger_rows(root=tmp_path)
    by_key = {f"{row['kind']}/{row['residue']}": row for row in rows}

    assert len(calls["assess"]) == 1
    assert len(calls["gaps"]) == 1
    assert calls["assess"][0][1]["extra_rows"] == frozenset({LedgerRowKey("source", "dimension-match")}) & SCOPED_DEBT_ROWS
    assert by_key["source/latent-distribution-gaussianity"]["status"] == "closed"
    assert by_key["source/transition-isotropy"]["status"] == "closed"
    assert by_key["source/dimension-match"]["status"] == "closed"
    assert by_key["source/finite-sample-support"]["status"] == "open"
    assert by_key["classifier/optimizer-certificate"]["status"] == "open"
    assert by_key["generalization/global-claim-boundary"]["status"] == "closed"
    assert {row["evidence_pointer"] for row in rows} == {"bedc_quality_lab.ledger.derive_ledger_gaps"}
    assert {row["owner"] for row in rows} == {"scripts.run_sigreg_training_proxy.build_payload"}
    assert all("terminal_verdict" not in row for row in rows)


def test_ledger_projection_consumes_structured_gap_objects(monkeypatch, tmp_path):
    monkeypatch.setattr(sigreg.run_sigreg_training_proxy, "build_payload", lambda **kwargs: fake_sigreg_payload())

    def fake_assess_debt(*args, **kwargs):
        return SimpleNamespace(
            items=(
                SimpleNamespace(kind="source", residue="latent-distribution-gaussianity", status="closed", severity="none"),
                SimpleNamespace(kind="source", residue="transition-isotropy", status="closed", severity="none"),
                SimpleNamespace(kind="source", residue="dimension-match", status="closed", severity="none"),
                SimpleNamespace(kind="source", residue="finite-sample-support", status="partial", severity="medium"),
                SimpleNamespace(kind="classifier", residue="optimizer-certificate", status="open", severity="high"),
                SimpleNamespace(kind="generalization", residue="global-claim-boundary", status="closed", severity="none"),
            )
        )

    def fake_derive_ledger_gaps(*args, **kwargs):
        return (
            SimpleNamespace(kind="source", residue="finite-sample-support", status="open", severity="high"),
            SimpleNamespace(kind="classifier", residue="optimizer-certificate", status="partial", severity="medium"),
        )

    monkeypatch.setattr(sigreg, "assess_debt", fake_assess_debt)
    monkeypatch.setattr(sigreg, "derive_ledger_gaps", fake_derive_ledger_gaps)

    rows = SIGRegBackendEvidenceAdapter().derive_ledger_rows(root=tmp_path)
    by_key = {f"{row['kind']}/{row['residue']}": row for row in rows}

    assert by_key["source/finite-sample-support"]["status"] == "open"
    assert by_key["source/finite-sample-support"]["severity"] == "high"
    assert by_key["classifier/optimizer-certificate"]["status"] == "partial"
    assert by_key["classifier/optimizer-certificate"]["severity"] == "medium"
    assert SIGRegBackendEvidenceAdapter().derive_negative_discovery_rows(root=tmp_path) == ()
    assert SIGRegBackendEvidenceAdapter().project_discovery_level(root=tmp_path) == rows
