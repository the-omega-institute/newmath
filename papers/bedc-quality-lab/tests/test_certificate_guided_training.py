import json
from types import SimpleNamespace

import pytest

import bedc_quality_lab
from bedc_quality_lab.cost_protocol import CostProtocol, NotClaimedPolicy, QualityFormula, REQUIRED_DEBT_ROWS
from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.metrics import QUALITY_Q_FORMULA_ID, quality_formula_description
from bedc_quality_lab.training.certificate_guided import (
    CertificateGuidedLossBreakdown,
    CertificateGuidedWeights,
    coverage_loss,
    ledger_loss,
    total_loss,
)
from scripts import run_certificate_guided_training as runner


def _protocol(name="shared-protocol"):
    return CostProtocol(
        name=name,
        row_weights={row: 0.10 + index * 0.01 for index, row in enumerate(sorted(REQUIRED_DEBT_ROWS))},
        quality_formula=QualityFormula(id=QUALITY_Q_FORMULA_ID, text=quality_formula_description()),
        not_claimed=NotClaimedPolicy(global_boundary=("outside",), treatment="Outside claims are excluded."),
    )


def _rows(status="open"):
    return [{"kind": row.kind, "residue": row.residue, "status": status} for row in sorted(REQUIRED_DEBT_ROWS)]


def _envelope(run_id, sample_count, use_torch):
    benefit = 0.40 if sample_count < 1000 else 0.38
    debt = 0.60 if sample_count < 1000 else 0.30
    cost = 0.03 if not use_torch else 0.06
    return SimpleNamespace(
        run_id=run_id,
        source_spec={"sample_count": sample_count, "source_count": 1, "mixing": "gaussian"},
        classifier_spec={
            "name": "tiny-mlp-2-128-128-2" if use_torch else "standardized-nonlinear-observation",
            "training": "align-cov-mean" if use_torch else "deterministic-standardization",
            "output_dim": 2,
            "cert_status": "not-certified",
        },
        stability_spec={},
        metrics={
            "actual_recovery_error": 0.70,
            "linear_identifiability_r2": 0.25,
            "approx_identifiability_proxy": 0.20,
            "quality_benefit": benefit,
            "quality_cost": cost,
            "quality_debt": debt,
            "quality_q": benefit - cost - debt,
            "quality_margin": benefit - cost - debt,
            "theorem_bound_recovery_pressure": 0.40,
        },
        artifacts={"envelope": runner.JSON_ARTIFACT, "report": runner.REPORT_ARTIFACT},
    )


def test_certificate_guided_training_closes_objective_and_report_loop(tmp_path):
    weights = CertificateGuidedWeights(lambda_s=2.0, lambda_m=3.0, lambda_l=5.0, lambda_c=7.0)
    breakdown = CertificateGuidedLossBreakdown(0.11, 0.13, 0.17, 0.19, True, False)
    assert total_loss(0.23, breakdown, weights) == pytest.approx(0.23 + 2 * 0.13 + 3 * 0.11 + 5 * 0.17 + 7 * 0.19)
    assert coverage_loss(0.25, 0.50) == pytest.approx(0.75)

    protocol = _protocol()
    assert ledger_loss(_rows(), protocol) == pytest.approx(sum(protocol.weight(row) for row in REQUIRED_DEBT_ROWS))
    with pytest.raises(ValueError, match="missing required debt rows"):
        ledger_loss(_rows()[:-1], protocol)

    saved = {
        "ROOT": runner.ROOT,
        "load_cost_protocol": runner.load_cost_protocol,
        "_gap_metrics": runner._gap_metrics,
        "run_experiment": runner.run_experiment,
    }
    try:
        runner.ROOT = tmp_path
        runner.load_cost_protocol = lambda: protocol
        runner._gap_metrics = lambda seed: {
            "source_run_id": f"gap-seed-{seed}",
            "vanilla": {"arm": "vanilla", "unlogged_error_rate": 0.1, "critical_unlogged_error_rate": 0.1},
            "gap_head": {"arm": "gap_head", "unlogged_error_rate": 0.6, "critical_unlogged_error_rate": 0.6},
        }
        runner.run_experiment = lambda **kwargs: _envelope(kwargs["run_id"], kwargs["sample_count"], kwargs["use_torch"])
        payload = runner._payload()
        runner.main()
    finally:
        for name, value in saved.items():
            setattr(runner, name, value)

    loaded = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert loaded["result"]["status"] == payload["result"]["status"] == "negative"
    assert {record["cost_protocol_name"] for record in payload["records"]} == {"shared-protocol"}
    assert all(record["ledger_rows"] for record in payload["records"])
    assert payload["deltas"]["after_minus_before"]["debt_delta"] < 0.0
    assert payload["deltas"]["after_minus_before"]["benefit_delta"] < 0.0
    assert payload["records"][1]["gap_metric_arm"] == "gap_head"
    assert payload["records"][0]["execution"]["deterministic_fallback"] is True
    assert payload["records"][2]["execution"]["torch_arm"] is True
    assert "shared-protocol" in report
    assert not hasattr(bedc_quality_lab, "CertificateGuidedWeights")
    from bedc_quality_lab.schema import SCHEMA_ID

    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
