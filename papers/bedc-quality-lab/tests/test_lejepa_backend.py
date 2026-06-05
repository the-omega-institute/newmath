from __future__ import annotations

from types import SimpleNamespace

from bedc_quality_lab import backends
from bedc_quality_lab.backends import lejepa
from bedc_quality_lab.backends.lejepa import LeJEPABackendEvidenceAdapter
from bedc_quality_lab.discovery_compiler.backend import BackendEvidenceAdapter, TheoryBackend
from bedc_quality_lab.discovery_compiler.compiler import load_adapter

EXPECTED_ASSUMPTIONS = (
    "gaussian_latent",
    "ou_transition",
    "dimension_match_m_equals_n",
    "population_optimum_or_empirical_proxy",
)
EXPECTED_METRICS = (
    "alignment_gap_delta_mse",
    "whitening_deviation_epsilon",
    "theorem3_bound_mse",
    "actual_recovery_mse",
    "linear_identifiability_r2",
)
EXPECTED_LEDGER_ROWS = (
    "source/latent-distribution-gaussianity",
    "source/transition-isotropy",
    "source/dimension-match",
    "source/finite-sample-support",
    "classifier/optimizer-certificate",
)


def fake_envelope():
    return SimpleNamespace(
        run_id="fake-delegated-run",
        source_spec={"latent_distribution": "fake-gaussian", "transition_isotropic": True},
        pattern_spec={"name": "fake-pattern"},
        classifier_spec={"cert_status": "fake-certified", "cert_threshold": {"theorem3_bound_mse": 12.5}},
        stability_spec={"seed": 99},
        metrics={
            "alignment_gap_delta_mse": 1.0,
            "whitening_deviation_epsilon": 2.0,
            "theorem3_bound_mse": 3.0,
            "actual_recovery_mse": 4.0,
            "linear_identifiability_r2": 5.0,
            "delegated_extra_metric": 6.0,
        },
        ledger_gaps=["kind=source; residue=finite-sample-support; severity=high; status=open"],
        debt_items=["kind=classifier; residue=optimizer-certificate; severity=medium; status=partial; score=0.5"],
        artifacts={
            "envelope": "reports/backend-probes/lejepa/fake-envelope.json",
            "report": "reports/backend-probes/lejepa/fake-report.md",
        },
        bedc_refs=["papers/bedc/fake.tex:pointer"],
    )


def test_adapter_metadata_and_module_loading_contract():
    adapter: BackendEvidenceAdapter = LeJEPABackendEvidenceAdapter()
    backend = adapter.backend

    assert isinstance(backend, TheoryBackend)
    assert backend.name == "lejepa"
    assert "lejepa" in backends.__all__
    assert lejepa.LeJEPABackendEvidenceAdapter is LeJEPABackendEvidenceAdapter
    assert load_adapter("bedc_quality_lab.backends.lejepa:LeJEPABackendEvidenceAdapter").backend.name == "lejepa"
    assert backend.assumptions == EXPECTED_ASSUMPTIONS
    assert backend.metrics == EXPECTED_METRICS
    assert tuple(f"{row['kind']}/{row['residue']}" for row in backend.ledger_rows) == EXPECTED_LEDGER_ROWS
    assert "terminal_verdict" not in backend.metrics
    assert all("terminal_verdict" not in row for row in backend.ledger_rows)


def test_compute_metrics_delegates_to_gaussian_ou_lejepa(monkeypatch, tmp_path):
    calls = []

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return fake_envelope()

    monkeypatch.setattr(lejepa.run_gaussian_ou_lejepa, "run_experiment", fake_run_experiment)

    payload = LeJEPABackendEvidenceAdapter().compute_metrics(root=tmp_path, generated_at="fake-time")

    assert calls == [
        {
            "run_id": "lejepa-backend-probe",
            "envelope_artifact": "reports/backend-probes/lejepa/evidence-envelope.json",
            "report_artifact": "reports/backend-probes/lejepa/quality-report.md",
        }
    ]
    assert payload["generated_at"] == "fake-time"
    assert tuple(payload["metrics"]) == LeJEPABackendEvidenceAdapter.backend.metrics
    assert "delegated_extra_metric" not in payload["metrics"]
    assert payload["classifier_spec"]["cert_status"] == "fake-certified"
    assert payload["classifier_spec"]["cert_threshold"]["theorem3_bound_mse"] == 12.5
    assert payload["source_spec"]["transition_isotropic"] is True
    assert payload["ledger_gaps"] == ["kind=source; residue=finite-sample-support; severity=high; status=open"]
    assert payload["artifacts"]["envelope"] == "reports/backend-probes/lejepa/fake-envelope.json"


def test_ledger_projection_consumes_delegated_gaps(monkeypatch, tmp_path):
    monkeypatch.setattr(lejepa.run_gaussian_ou_lejepa, "run_experiment", lambda **kwargs: fake_envelope())

    adapter = LeJEPABackendEvidenceAdapter()
    rows = adapter.derive_ledger_rows(root=tmp_path)
    by_key = {f"{row['kind']}/{row['residue']}": row for row in rows}

    assert by_key["source/finite-sample-support"]["status"] == "open"
    assert by_key["source/finite-sample-support"]["severity"] == "high"
    assert by_key["source/dimension-match"]["status"] == "declared"
    assert {row["owner"] for row in rows} == {"scripts.run_gaussian_ou_lejepa.run_experiment"}
    assert all("terminal_verdict" not in row for row in rows)
    assert adapter.derive_negative_discovery_rows(root=tmp_path) == ()
    assert adapter.project_discovery_level(root=tmp_path) == rows
