import json
from copy import deepcopy

import pytest

from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map
from scripts import run_sigreg_training_proxy as runner


def _payload(**kwargs):
    params = {
        "run_id": "fixture",
        "generated_at": "fixture-time",
        "sample_count": 64,
        "steps": 1,
        "seeds": (17,),
        "directions": 4,
        "frequencies": (0.5, 1.0),
        "use_torch": True,
    }
    params.update(kwargs)
    return runner.build_payload(**params)


def _fallback_payload(**kwargs):
    return _payload(use_torch=False, **kwargs)


def _rebuilt_payload(records, **kwargs):
    params = {
        "records": records,
        "run_id": "fixture",
        "generated_at": "fixture-time",
        "sample_count": 64,
        "steps": 1,
        "seeds": (17,),
        "lambda_sigreg": runner.DEFAULT_LAMBDA_SIGREG,
        "directions": 4,
        "frequencies": (0.5, 1.0),
        "learning_rate": runner.DEFAULT_LEARNING_RATE,
        "json_artifact": runner.JSON_ARTIFACT,
        "report_artifact": runner.REPORT_ARTIFACT,
    }
    params.update(kwargs)
    return runner._payload_from_records(**params)


def _demoted_together(payload, failed_gate):
    spec = canonical._specs_by_name()["sigreg-training-proxy"]
    row = discovery_map.discovery_row(spec, runner.canonical_summary_payload(payload))

    assert payload["d1_evidence"]["d1_hardgates"][failed_gate]["status"] == "fail"
    assert payload["claim_gate"]["status"] == "fail"
    assert payload["claim_gate"]["training_audit_improvement_tradeoff"] is False
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["failed_gate"] == failed_gate
    assert payload["failed_gate"] == failed_gate
    assert payload["claim_capsule"]["claim_status"] == "failed"
    assert payload["result"]["status"] == "negative"
    assert payload["result"]["terminal_verdict"] == "rejected"
    assert payload["result"]["discovery_level"] == "DN"
    assert row["discovery_level"] == "DN"
    assert row["terminal_verdict"] == "rejected"
    assert row["audit_status"] == "valid"


def test_exact_four_arms_and_sigreg_loss_formula():
    payload = _payload(lambda_sigreg=0.35)
    records = payload["raw_records"]
    true_record = next(record for record in records if record["arm"] == "true_sigreg_sliced_cf")
    metrics = true_record["training_loss"]
    expected = (1.0 - 0.35) * metrics["alignment"] + 0.35 * metrics["sigreg_sliced_cf"]

    assert tuple(payload["arm_protocol"]["arms"]) == runner.ARMS
    assert set(payload["arm_summaries"]) == set(runner.ARMS)
    assert len(payload["arm_summaries"]) == 4
    assert metrics["loss"] == pytest.approx(expected)


def test_d1_hardgates_and_boundary_nonclaims_are_recorded():
    payload = _payload()
    gates = payload["d1_evidence"]["d1_hardgates"]

    assert set(gates) == {"D1-HG1", "D1-HG2", "D1-HG3", "D1-HG4", "D1-HG5"}
    assert all(row["status"] == "pass" for row in gates.values())
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert payload["forbidden_claim_term_audit"]["hits"] == []
    assert payload["result"]["status"] == "d1-pointer-accepted"
    assert gates["D1-HG1"]["record_count"] == 1
    assert gates["D1-HG2"]["evidence"].startswith("SIGReg objective and covariance proxy")
    assert gates["D1-HG3"]["tradeoff"]["ledger"] == "recorded"
    assert gates["D1-HG4"]["full_lejepa_claim"] is False
    assert gates["D1-HG5"]["hits"] == []
    for item in runner.NOT_CLAIMED:
        assert item in payload["not_claimed"]
        assert item in payload["claim_capsule"]["not_claimed"]


def test_fallback_sigreg_record_fails_hg1_and_demotes_together():
    payload = _fallback_payload()

    _demoted_together(payload, "D1-HG1")
    assert payload["d1_evidence"]["d1_hardgates"]["D1-HG1"]["record_count"] == 0


def test_hg2_objective_proxy_collapse_demotes_together():
    records = deepcopy(_payload()["raw_records"])
    sigreg_value = next(row for row in records if row["arm"] == "true_sigreg_sliced_cf")["evaluation"]["sigreg_sliced_cf"]
    for row in records:
        if row["arm"] == "covariance_proxy_current":
            row["evaluation"]["sigreg_sliced_cf"] = sigreg_value
    payload = _rebuilt_payload(records)

    _demoted_together(payload, "D1-HG2")


def test_hg3_tradeoff_failure_demotes_together():
    records = deepcopy(_payload()["raw_records"])
    alignment_row = next(row for row in records if row["arm"] == "alignment_only")
    for row in records:
        if row["arm"] == "true_sigreg_sliced_cf":
            row["evaluation"]["sigreg_sliced_cf"] = alignment_row["evaluation"]["sigreg_sliced_cf"] + 1.0
            row["evaluation"]["alignment"] = alignment_row["evaluation"]["alignment"] - 1.0e-6
    payload = _rebuilt_payload(records)

    _demoted_together(payload, "D1-HG3")
    tradeoff = payload["d1_evidence"]["d1_hardgates"]["D1-HG3"]["tradeoff"]
    assert tradeoff["sigreg_improves_gaussianity_vs_alignment_only"] is False
    assert tradeoff["sigreg_hurts_alignment_vs_alignment_only"] is False


def test_hg4_full_sweep_boundary_failure_demotes_together():
    payload = _rebuilt_payload(
        deepcopy(_payload()["raw_records"]),
        full_sweep_requirements={"2D mixings": True},
        full_lejepa_claim=True,
    )

    _demoted_together(payload, "D1-HG4")


def test_hg5_forbidden_claim_term_failure_demotes_together():
    payload = _rebuilt_payload(
        deepcopy(_payload()["raw_records"]),
        positive_claim={
            "text": "full-lejepa SIGReg training proxy",
            "scope": "lab-local Gaussian-OU toy encoder training proxy",
        },
    )

    _demoted_together(payload, "D1-HG5")
    assert payload["d1_evidence"]["d1_hardgates"]["D1-HG5"]["hits"] == ["full-lejepa"]
    assert not (
        payload["forbidden_claim_term_audit"]["status"] == "fail"
        and payload["result"]["status"] == "d1-pointer-accepted"
    )


def test_claim_capsule_and_run_artifacts_are_written(tmp_path):
    payload = _payload(run_id="d1-test")

    runner.write_artifacts(payload, root=tmp_path)

    run_dir = tmp_path / "reports" / "runs" / "d1-test"
    capsule = json.loads((run_dir / "claim_capsule.json").read_text(encoding="utf-8"))
    raw_lines = (run_dir / "raw_metrics.jsonl").read_text(encoding="utf-8").strip().splitlines()
    summary = json.loads((run_dir / "summary.json").read_text(encoding="utf-8"))
    snapshot = json.loads((run_dir / "result_snapshot.json").read_text(encoding="utf-8"))
    canonical_summary = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert capsule["schema_id"] == runner.CLAIM_CAPSULE_SCHEMA_ID
    assert capsule["forbidden_claim_term_audit"]["status"] == "pass"
    assert len(raw_lines) == len(runner.ARMS)
    assert summary["run_artifacts"]["claim_capsule"] == "reports/runs/d1-test/claim_capsule.json"
    assert snapshot == payload["result_snapshot"]
    assert "claim_capsule" not in canonical_summary
    assert "result_snapshot" not in canonical_summary
    assert canonical_summary["claim_capsule_ref"]["artifact"] == "reports/runs/d1-test/claim_capsule.json"
    assert canonical_summary["result_snapshot_ref"]["artifact"] == "reports/runs/d1-test/result_snapshot.json"
    assert (run_dir / "report.md").exists()
    assert (tmp_path / runner.JSON_ARTIFACT).exists()
    assert (tmp_path / runner.REPORT_ARTIFACT).exists()


def test_canonical_pointer_row_and_discovery_projection():
    spec = canonical._specs_by_name()["sigreg-training-proxy"]
    payload = _payload(json_artifact=spec.json_artifact, report_artifact=spec.markdown_artifact)
    row = discovery_map.discovery_row(spec, payload)

    assert spec.command == ("python3", "scripts/run_sigreg_training_proxy.py")
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.arm_protocol"
    assert spec.cost_pointer == "$.source_artifacts.cost_protocol"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert spec.positive_claim_pointer == "$.positive_claim"
    assert spec.no_control_rationale_pointer == "$.full_lejepa_boundary"
    assert row["report"] == "sigreg-training-proxy"
    assert row["discovery_level"] == "D1"
    assert row["terminal_verdict"] == payload["result"]["terminal_verdict"]
    assert row["debt_row_pointer"] == "$.d1_evidence.debt_delta"
    assert row["audit_status"] == "valid"


def test_discovery_projection_rejects_status_cell_mismatch():
    spec = canonical._specs_by_name()["sigreg-training-proxy"]
    payload = runner.canonical_summary_payload(_payload(json_artifact=spec.json_artifact, report_artifact=spec.markdown_artifact))
    payload["claim_gate"]["status"] = "fail"
    row = discovery_map.discovery_row(spec, payload)

    assert row["discovery_level"] == "DN"
    assert row["terminal_verdict"] == "rejected"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "sigreg-claim_gate_status-mismatch"


def test_discovery_projection_rejects_forbidden_audit_fail_with_accepted_result():
    spec = canonical._specs_by_name()["sigreg-training-proxy"]
    payload = runner.canonical_summary_payload(_payload(json_artifact=spec.json_artifact, report_artifact=spec.markdown_artifact))
    payload["forbidden_claim_term_audit"] = {
        "status": "fail",
        "forbidden_positive_claim_terms": ["full-lejepa"],
        "hits": ["full-lejepa"],
    }
    row = discovery_map.discovery_row(spec, payload)

    assert payload["result"]["status"] == "d1-pointer-accepted"
    assert row["discovery_level"] == "DN"
    assert row["terminal_verdict"] == "rejected"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "sigreg-forbidden_audit_status-mismatch"


def test_canonical_denominators_include_sigreg_training_proxy(tmp_path, monkeypatch):
    from tests.test_canonical_reports import _write_payloads_for_all_specs

    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    _write_payloads_for_all_specs(canonical, tmp_path)

    reports = [
        {
            "name": spec.name,
            "json_artifact": spec.json_artifact,
            "status": "pass",
        }
        for spec in canonical.CANONICAL_REPORTS
    ]
    scorecard = canonical._build_quality_scorecard(reports, generated_at="fixture-time")
    by_metric = {row["metric"]: row for row in scorecard["rows"]}

    assert by_metric["ScopeCompleteness"]["denominator"] == 14
    assert by_metric["CostProtocolCompleteness"]["denominator"] == 14
