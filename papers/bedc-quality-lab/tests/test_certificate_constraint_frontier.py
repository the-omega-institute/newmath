import json

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_certificate_constraint_frontier as runner


def _record(arm, role, seed, task, uer, benefit, debt, q=None):
    return {
        "arm": arm,
        "role": role,
        "candidate_id": f"{arm}-candidate",
        "seed": seed,
        "performance": {"task_loss": task},
        "unlogged_error_rate": uer,
        "quality_benefit": benefit,
        "quality_debt": debt,
        "quality_q": benefit - debt if q is None else q,
    }


def _source(*, tradeoff=True, positive_gate=False, ci_low=-0.1, net_information=None):
    records = []
    for seed in (1, 2):
        records.extend(
            [
                _record("baseline", "before", seed, 1.0, 0.50, 0.80, 1.00),
                _record("debt_only", "debt_only", seed, 0.80, 0.40, 0.70, 0.60),
                _record("benefit_only", "benefit_only", seed, 0.70, 0.30, 1.20, 1.20),
                _record(
                    "debt_plus_benefit",
                    "after",
                    seed,
                    0.60,
                    0.20,
                    0.60 if tradeoff else 1.10,
                    0.50,
                ),
                _record("matched_random_debt", "control", seed, 0.90, 0.45, 0.75, 0.90),
            ]
        )
    source = {
        "records": records,
        "deltas": {
            "after_minus_before": {
                "debt_delta": -0.50,
                "benefit_delta": -0.20 if tradeoff else 0.30,
                "quality_q_delta": 0.30,
            },
            "debt_plus_benefit_minus_baseline": {
                "debt_delta": -0.50,
                "benefit_delta": -0.20 if tradeoff else 0.30,
                "quality_q_delta": 0.30,
            },
        },
        "claim_gate": {
            "positive_quality_improvement": positive_gate,
            "blockers": [] if positive_gate else ["quality-q-ci95-low-nonpositive"],
        },
        "hardgate": {
            "status": "positive" if positive_gate else "non-positive",
            "failed_gate": "audit-improvement-tradeoff" if tradeoff else None,
            "basis": {
                "main_arm": "debt_plus_benefit",
                "baseline_arm": "baseline",
                "debt_delta": -0.50,
                "benefit_delta": -0.20 if tradeoff else 0.30,
            },
        },
        "paired_delta_ci": {
            "after_minus_before": {
                "quality_q_delta": {
                    "status": "ok",
                    "ci95_low": ci_low,
                }
            }
        },
        "arm_protocol": {
            "main_pair": ["baseline", "debt_plus_benefit"],
            "control_pair": ["baseline", "matched_random_debt"],
        },
        "source_artifacts": {"generation_script": "scripts/run_certificate_guided_training.py"},
        "lambda_weights": {"lambda_s": 0.25, "lambda_m": 0.50, "lambda_l": 0.75, "lambda_c": 1.00},
        "cost_protocol": {"name": "fixture-cost-protocol"},
        "failed_gate": "audit-improvement-tradeoff" if tradeoff else None,
    }
    if net_information is not None:
        source["net_information"] = net_information
    return source


def _row(payload, threshold_id, arm):
    return next(
        row
        for row in payload["constraint_rows"]
        if row["threshold_id"] == threshold_id and row["arm"] == arm
    )


def test_threshold_grid_sources_are_traceable():
    payload = runner.build_payload(_source(), generated_at="2030-01-01T00:00:00+00:00")

    assert payload["schema_id"] == runner.LOCAL_SCHEMA_ID
    assert payload["threshold_grid"]
    assert payload["threshold_source_policy"] == {
        "alpha": "observed UER quantiles from arm means",
        "beta": "baseline benefit and candidate benefit bands from arm means",
        "gamma": "baseline debt and candidate debt bands from arm means",
        "lambda_weight_source": "$.lambda_weights",
        "cost_weight_source": "$.cost_protocol",
        "hidden_weight": False,
        "combined_quality_metric": False,
    }
    for threshold in payload["threshold_grid"]:
        assert threshold["constraint"] == "min task_loss subject to UER<=alpha, Benefit>=beta, Debt<=gamma"
        assert threshold["alpha_source"]["source_pointer"] == "$.records[*].unlogged_error_rate"
        assert "benefit" in threshold["beta_source"]["source_pointer"]
        assert "debt" in threshold["gamma_source"]["source_pointer"]
    assert any(t["alpha_source"]["source"] == "observed_uer_quantile_0.5" for t in payload["threshold_grid"])
    assert any(t["beta_source"]["source"] == "baseline_mean_benefit" for t in payload["threshold_grid"])
    assert any(t["gamma_source"]["source"] == "baseline_mean_debt" for t in payload["threshold_grid"])


def test_constraint_rows_compute_per_arm_feasibility():
    source = _source()
    summaries = runner._arm_means(source["records"])
    grid = [
        {
            "threshold_id": "fixture",
            "alpha": 0.25,
            "beta": 0.55,
            "gamma": 0.55,
        }
    ]
    rows = runner._constraint_rows(summaries, grid)

    baseline = next(row for row in rows if row["arm"] == "baseline")
    candidate = next(row for row in rows if row["arm"] == "debt_plus_benefit")

    assert baseline["uer_ok"] is False
    assert baseline["benefit_ok"] is True
    assert baseline["debt_ok"] is False
    assert baseline["feasible"] is False
    assert candidate["uer_ok"] is True
    assert candidate["benefit_ok"] is True
    assert candidate["debt_ok"] is True
    assert candidate["feasible"] is True
    assert candidate["task_loss"] == 0.60
    assert candidate["evidence_status"] == "constraint-satisfied local candidate"
    assert candidate["positive"] is False


def test_frontier_selects_min_task_loss_feasible_and_marks_infeasible():
    source = _source()
    summaries = runner._arm_means(source["records"])
    grid = [
        {"threshold_id": "feasible", "alpha": 0.45, "beta": 0.55, "gamma": 0.70},
        {"threshold_id": "none", "alpha": 0.10, "beta": 2.0, "gamma": 0.10},
    ]
    rows = runner._constraint_rows(summaries, grid)
    frontier = runner._frontier(grid, rows, positive_pointer_allowed=False)

    feasible = next(cell for cell in frontier if cell["threshold_id"] == "feasible")
    infeasible = next(cell for cell in frontier if cell["threshold_id"] == "none")

    assert feasible["status"] == "constraint-satisfied local candidate"
    assert feasible["candidate"]["arm"] == "debt_plus_benefit"
    assert feasible["candidate"]["task_loss"] == 0.60
    assert feasible["positive"] is False
    assert infeasible["status"] == "infeasible"
    assert infeasible["verdict"] == "rejected"
    assert infeasible["discovery_level"] == "DN"
    assert infeasible["candidate"] is None


def test_hg_ccf_1_debt_down_benefit_down_is_non_positive_dn_or_d1_bound():
    payload = runner.build_payload(
        _source(tradeoff=True, positive_gate=True, ci_low=0.1, net_information=1.0),
        generated_at="2030-01-01T00:00:00+00:00",
    )

    gate = payload["hardgate"]["gates"]["HG-CCF-1"]
    assert gate["status"] == "fail"
    assert gate["failed_gate"] == "audit-improvement-tradeoff"
    assert gate["positive"] is False
    assert gate["discovery_level_bound"] == "DN_or_D1"
    assert payload["hardgate"]["failed_gate"] == "audit-improvement-tradeoff"
    assert payload["hardgate"]["positive"] is False
    assert payload["hardgate"]["discovery_level"] == "DN"
    assert "audit-improvement-tradeoff" in payload["hardgate"]["blockers"]


def test_hg_ccf_1_tradeoff_demotes_every_feasible_frontier_cell():
    payload = runner.build_payload(
        _source(tradeoff=True, positive_gate=True, ci_low=0.1, net_information=1.0),
        generated_at="2030-01-01T00:00:00+00:00",
    )

    feasible = [cell for cell in payload["frontier"] if cell["status"] != "infeasible"]

    assert feasible
    for cell in feasible:
        assert cell["positive"] is False
        assert cell["discovery_level"] == "DN"


def test_hg_ccf_2_feasible_cell_is_only_local_candidate_without_existing_positive_gates():
    payload = runner.build_payload(
        _source(tradeoff=False, positive_gate=False, ci_low=0.1, net_information=1.0),
        generated_at="2030-01-01T00:00:00+00:00",
    )

    feasible = next(cell for cell in payload["frontier"] if cell["status"] != "infeasible")
    gate = payload["hardgate"]["gates"]["HG-CCF-2"]

    assert feasible["status"] == "constraint-satisfied local candidate"
    assert feasible["positive"] is False
    assert feasible["discovery_level"] == "DN"
    assert gate["status"] == "pass"
    assert gate["positive_pointer_allowed"] is False
    assert payload["hardgate"]["basis"]["positive_pointer_gate"]["training_positive_gate"] is False
    assert "positive-pointer-gate-not-satisfied" in payload["hardgate"]["blockers"]


def test_hg_ccf_2_non_tradeoff_positive_gate_can_mark_feasible_frontier_cell():
    payload = runner.build_payload(
        _source(tradeoff=False, positive_gate=True, ci_low=0.1, net_information=1.0),
        generated_at="2030-01-01T00:00:00+00:00",
    )

    feasible = [cell for cell in payload["frontier"] if cell["status"] != "infeasible"]
    gate = payload["hardgate"]["gates"]["HG-CCF-2"]

    assert feasible
    assert gate["status"] == "pass"
    assert gate["positive_pointer_allowed"] is True
    assert payload["hardgate"]["gates"]["HG-CCF-1"]["status"] == "pass"
    assert any(cell["positive"] is True for cell in feasible)
    assert all(cell["discovery_level"] == "D1" for cell in feasible)


def test_hg_ccf_3_no_feasible_cell_is_rejected_dn():
    source = _source(tradeoff=False)
    summaries = runner._arm_means(source["records"])
    grid = [{"threshold_id": "none", "alpha": 0.01, "beta": 5.0, "gamma": 0.01}]
    rows = runner._constraint_rows(summaries, grid)
    frontier = runner._frontier(grid, rows, positive_pointer_allowed=False)
    hardgate = runner._hardgate(
        source,
        frontier,
        rows,
        runner._positive_pointer_allowed(source)[1],
    )

    assert frontier[0]["status"] == "infeasible"
    assert hardgate["status"] == "rejected"
    assert hardgate["failed_gate"] == "no-feasible-constraint-cell"
    assert hardgate["discovery_level"] == "DN"
    assert hardgate["gates"]["HG-CCF-3"]["status"] == "fail"


def test_hg_ccf_4_constraint_failures_are_non_positive():
    source = _source(tradeoff=False)
    summaries = runner._arm_means(source["records"])
    grid = [{"threshold_id": "partial", "alpha": 0.50, "beta": 0.90, "gamma": 0.70}]
    rows = runner._constraint_rows(summaries, grid)
    hardgate = runner._hardgate(
        source,
        runner._frontier(grid, rows, positive_pointer_allowed=False),
        rows,
        runner._positive_pointer_allowed(source)[1],
    )

    failed = _row({"constraint_rows": rows}, "partial", "debt_only")
    assert failed["uer_ok"] is True
    assert failed["benefit_ok"] is False
    assert failed["debt_ok"] is True
    assert failed["feasible"] is False
    assert failed["evidence_status"] == "non-positive"
    assert hardgate["gates"]["HG-CCF-4"]["status"] == "fail"
    assert "benefit-or-debt-constraint-not-satisfied-for-some-cells" in hardgate["blockers"]


def test_hg_ccf_5_no_hidden_weight_or_total_score():
    payload = runner.build_payload(_source(), generated_at="2030-01-01T00:00:00+00:00")
    text = json.dumps(payload).lower()
    gate = payload["hardgate"]["gates"]["HG-CCF-5"]

    assert gate["status"] == "pass"
    assert gate["hidden_weight"] is False
    assert gate["combined_quality_metric"] is False
    assert "total_score" not in payload["threshold_source_policy"]
    assert "quality grade" not in text
    assert "discovery score" not in text


def test_hg_ccf_6_sidecar_schema_boundary_and_forbidden_terms():
    payload = runner.build_payload(_source(), generated_at="2030-01-01T00:00:00+00:00")
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    gate = payload["hardgate"]["gates"]["HG-CCF-6"]
    text = json.dumps(payload).lower()

    assert runner.JSON_ARTIFACT not in json_artifacts
    assert "certificate-constraint-frontier" not in names
    assert payload["schema_id"] == runner.LOCAL_SCHEMA_ID
    assert payload["schema_id"] != SCHEMA_ID
    assert gate["shared_schema_id_reused"] is False
    assert gate["forbidden_positive_claim_term_hits"] == []
    for term in runner.FORBIDDEN_POSITIVE_CLAIM_TERMS:
        assert term.lower() not in text
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]


def test_write_payload_creates_reports_sidecar(tmp_path):
    payload = runner.build_payload(_source(), generated_at="2030-01-01T00:00:00+00:00")

    runner.write_payload(payload, tmp_path)

    loaded = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert loaded["schema_id"] == runner.LOCAL_SCHEMA_ID
    assert loaded["artifact"] == runner.JSON_ARTIFACT
    assert "# Certificate Constraint Frontier" in markdown
    assert "No hidden cost weight" in markdown
