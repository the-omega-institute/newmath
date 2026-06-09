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
    seed = int(run_id.rsplit("-seed-", 1)[1])
    benefit = 0.40 + 0.001 * seed if sample_count < 1000 else 0.38 + 0.001 * seed
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


def _positive_ci_record(role, seed, quality_q, *, protocol="shared", split="same"):
    return {
        "role": role,
        "seed": seed,
        "quality_q": quality_q,
        "quality_benefit": quality_q + 1.0,
        "quality_cost": 0.1,
        "quality_debt": 0.2,
        "certificate_guided_loss": 1.0 - quality_q,
        "cost_protocol_name": protocol,
        "split_fingerprint": split,
        "ledger_rows": [{"kind": "k", "residue": "r"}],
    }


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
    assert {record["arm"] for record in payload["records"]} == {
        "baseline",
        "debt_only",
        "benefit_only",
        "debt_plus_benefit",
        "matched_random_debt",
    }
    assert {record["role"] for record in payload["records"]} == {"before", "debt_only", "benefit_only", "after", "control"}
    assert len(payload["records"]) == 5 * len(runner.SEEDS)
    for seed in runner.SEEDS:
        assert [record["arm"] for record in payload["records"] if record["seed"] == seed] == [
            "baseline",
            "debt_only",
            "benefit_only",
            "debt_plus_benefit",
            "matched_random_debt",
        ]
    assert all(record["ledger_rows"] for record in payload["records"])
    assert len({record["split_fingerprint"] for record in payload["records"]}) == 1
    assert payload["deltas"]["after_minus_before"]["debt_delta"] < 0.0
    assert payload["deltas"]["after_minus_before"]["benefit_delta"] < 0.0
    assert payload["deltas"]["debt_plus_benefit_minus_baseline"] == payload["deltas"]["after_minus_before"]
    assert payload["deltas"]["matched_random_debt_minus_baseline"] == payload["deltas"]["control_minus_before"]
    assert payload["records"][1]["gap_metric_arm"] == "gap_head"
    assert payload["records"][0]["execution"]["deterministic_fallback"] is True
    assert payload["records"][4]["execution"]["torch_arm"] is True
    assert payload["paired_seed_protocol"]["seeds"] == list(runner.SEEDS)
    assert payload["paired_seed_protocol"]["main_pair"] == ["before", "after"]
    assert payload["paired_seed_protocol"]["control_pair"] == ["before", "control"]
    assert payload["arm_protocol"]["main_pair"] == ["baseline", "debt_plus_benefit"]
    assert payload["arm_protocol"]["control_pair"] == ["baseline", "matched_random_debt"]
    assert payload["arm_protocol"]["compat_roles"] == {
        "before": "baseline",
        "after": "debt_plus_benefit",
        "control": "matched_random_debt",
    }
    after_ci = payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]
    assert after_ci["status"] == "ok"
    assert after_ci["n"] == len(runner.SEEDS)
    main_summary = payload["arm_summaries"]["debt_plus_benefit"]
    assert main_summary["delta_vs_baseline"] == payload["deltas"]["after_minus_before"]
    assert main_summary["paired_ci_vs_baseline"]["quality_q_delta"] == after_ci
    assert payload["arm_summaries"]["matched_random_debt"]["delta_vs_baseline"] == payload["deltas"]["control_minus_before"]
    assert payload["claim_gate"]["paired_ci_status"] == "ok"
    assert payload["claim_gate"]["audit_improvement_tradeoff"] is True
    assert payload["claim_gate"]["positive_quality_improvement"] is False
    assert "audit-improvement-tradeoff" in payload["claim_gate"]["blockers"]
    assert payload["hardgate"]["status"] == "non-positive"
    assert payload["hardgate"]["failed_gate"] == "audit-improvement-tradeoff"
    assert payload["failed_gate"] == "audit-improvement-tradeoff"
    assert payload["verdict"] == "demoted"
    assert payload["discovery_level"] == "DN"
    assert any("benefit decline" in item for item in payload["not_claimed"])
    assert "shared-protocol" in report
    assert "## Paired-Seed CI" in report
    assert "## Claim Gate" in report
    assert "Audit improvement tradeoff: `true`" in report
    assert "Mechanical quality gate: `false`" in report
    assert "Mechanical quality gate: `true`" not in report
    assert "positive quality wording is not claimed" in report
    assert not hasattr(bedc_quality_lab, "CertificateGuidedWeights")
    from bedc_quality_lab.schema import SCHEMA_ID

    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"


def test_claim_gate_requires_ci_lower_above_zero_even_when_mean_is_positive():
    records = []
    for seed, delta in enumerate([0.1, 0.1, 0.7], start=1):
        records.append(_positive_ci_record("before", seed, 1.0))
        records.append(_positive_ci_record("after", seed, 1.0 + delta))
        records.append(_positive_ci_record("control", seed, 0.9))
    paired_ci = runner._paired_delta_ci(records)
    gate = runner._claim_gate(records, paired_ci)

    assert paired_ci["after_minus_before"]["quality_q_delta"]["mean"] > 0.0
    assert paired_ci["after_minus_before"]["quality_q_delta"]["ci95_low"] <= 0.0
    assert gate["positive_quality_improvement"] is False
    assert "quality-q-ci95-low-nonpositive" in gate["blockers"]


def test_claim_gate_turns_positive_only_for_same_cost_same_split_complete_positive_ci():
    records = []
    for seed in (1, 2, 3):
        records.append(_positive_ci_record("before", seed, 1.0))
        records.append(_positive_ci_record("after", seed, 1.4))
        records.append(_positive_ci_record("control", seed, 0.9))
    paired_ci = runner._paired_delta_ci(records)

    gate = runner._claim_gate(records, paired_ci)

    assert paired_ci["after_minus_before"]["quality_q_delta"]["status"] == "ok"
    assert paired_ci["after_minus_before"]["quality_q_delta"]["ci95_low"] > 0.0
    assert gate["positive_quality_improvement"] is True
    assert gate["blockers"] == []

    records[1]["cost_protocol_name"] = "other"
    mismatch_ci = runner._paired_delta_ci(records)
    mismatch_gate = runner._claim_gate(records, mismatch_ci)
    assert mismatch_gate["positive_quality_improvement"] is False
    assert "cost-protocol-mismatch" in mismatch_gate["blockers"]


def test_claim_gate_blocks_positive_for_ci_positive_tradeoff():
    records = []
    for seed in (1, 2, 3):
        before = _positive_ci_record("before", seed, 1.0)
        after = _positive_ci_record("after", seed, 1.4)
        control = _positive_ci_record("control", seed, 0.9)
        before["quality_benefit"] = 2.0
        before["quality_debt"] = 1.0
        after["quality_benefit"] = 1.5
        after["quality_debt"] = 0.5
        records.extend([before, after, control])
    paired_ci = runner._paired_delta_ci(records)
    gate = runner._claim_gate(records, paired_ci)

    assert paired_ci["after_minus_before"]["quality_q_delta"]["status"] == "ok"
    assert paired_ci["after_minus_before"]["quality_q_delta"]["ci95_low"] > 0.0
    assert gate["audit_improvement_tradeoff"] is True
    assert gate["positive_quality_improvement"] is False
    assert "audit-improvement-tradeoff" in gate["blockers"]


def test_claim_gate_blocks_positive_for_split_or_shape_mismatch():
    records = []
    for seed in (1, 2, 3):
        records.append(_positive_ci_record("before", seed, 1.0))
        records.append(_positive_ci_record("after", seed, 1.4))
        records.append(_positive_ci_record("control", seed, 0.9))
    records[1]["split_fingerprint"] = "other"
    split_ci = runner._paired_delta_ci(records)
    split_gate = runner._claim_gate(records, split_ci)

    assert split_gate["positive_quality_improvement"] is False
    assert "split-fingerprint-mismatch" in split_gate["blockers"]

    incomplete = [record for record in records if not (record["role"] == "control" and record["seed"] == 3)]
    shape_gate = runner._claim_gate(incomplete, runner._paired_delta_ci(incomplete))
    assert shape_gate["positive_quality_improvement"] is False
    assert "missing-before-after-control" in shape_gate["blockers"]
