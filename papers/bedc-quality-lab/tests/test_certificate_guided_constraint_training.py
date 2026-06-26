import json
from types import SimpleNamespace

import bedc_quality_lab
import pytest
from bedc_quality_lab.cost_protocol import CostProtocol, NotClaimedPolicy, QualityFormula, REQUIRED_DEBT_ROWS, SCOPED_DEBT_ROWS
from bedc_quality_lab.metrics import QUALITY_Q_FORMULA_ID, quality_formula_description
from bedc_quality_lab.training.certificate_guided import (
    ConstraintLambdas,
    ConstraintThresholds,
    constrained_lagrangian_loss,
)
from scripts import run_canonical_reports as canonical
from scripts import run_certificate_guided_constraint_training as runner


def _protocol(name="shared-protocol"):
    return CostProtocol(
        name=name,
        row_weights={row: 0.10 + index * 0.01 for index, row in enumerate(sorted(REQUIRED_DEBT_ROWS | SCOPED_DEBT_ROWS))},
        quality_formula=QualityFormula(id=QUALITY_Q_FORMULA_ID, text=quality_formula_description()),
        not_claimed=NotClaimedPolicy(global_boundary=("outside",), treatment="Outside claims are excluded."),
    )


def _envelope(run_id, seed):
    benefit = 0.42 + 0.001 * (seed % 7)
    cost = 0.04
    debt = 0.82
    q = benefit - cost - debt
    return SimpleNamespace(
        run_id=run_id,
        source_spec={"sample_count": runner.SAMPLE_COUNT, "source_count": 1, "mixing": "gaussian"},
        classifier_spec={
            "name": "standardized-nonlinear-observation",
            "training": "deterministic-standardization",
            "output_dim": 2,
            "cert_status": "not-certified",
        },
        stability_spec={},
        metrics={
            "actual_recovery_error": 0.18,
            "linear_identifiability_r2": 0.70,
            "approx_identifiability_proxy": 0.65,
            "quality_benefit": benefit,
            "quality_cost": cost,
            "quality_debt": debt,
            "quality_q": q,
            "quality_margin": q,
            "theorem_bound_recovery_pressure": 0.10,
        },
        artifacts={"envelope": runner.JSON_ARTIFACT, "report": runner.REPORT_ARTIFACT},
    )


def _gap_metrics(seed):
    return {
        "source_run_id": f"gap-seed-{seed}",
        "vanilla": {
            "arm": "vanilla",
            "unlogged_error_rate": 0.50,
            "critical_unlogged_error_rate": 0.30,
        },
        "gap_head": {
            "arm": "gap_head",
            "unlogged_error_rate": 0.49,
            "critical_unlogged_error_rate": 0.28,
        },
    }


def _patched_payload(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(runner, "load_cost_protocol", lambda: _protocol())
    monkeypatch.setattr(runner, "_gap_metrics", _gap_metrics)
    monkeypatch.setattr(
        runner,
        "run_experiment",
        lambda **kwargs: _envelope(kwargs["run_id"], kwargs["seed"]),
    )
    return runner._payload(run_id="fixture-c1")


def _pointer_value(payload, pointer):
    cursor = payload
    assert pointer.startswith("$.")
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                assert isinstance(cursor, dict)
                assert key in cursor
                cursor = cursor[key]
            index_text = bracket[:-1]
            assert index_text.isdigit()
            assert isinstance(cursor, list)
            cursor = cursor[int(index_text)]
            part = ""
        if not part:
            continue
        if isinstance(cursor, dict):
            assert part in cursor
            cursor = cursor[part]
            continue
        assert isinstance(cursor, list)
        assert part.isdigit()
        cursor = cursor[int(part)]
    return cursor


def _assert_artifact_pointer_resolves(root, payload, artifact_pointer):
    artifact, pointer = artifact_pointer.split(":", 1)
    path = root / artifact
    assert path.exists()
    pointed_payload = json.loads(path.read_text(encoding="utf-8"))
    assert _pointer_value(pointed_payload, pointer) is not None


def _artifact_pointer_value(root, artifact_pointer):
    artifact, pointer = artifact_pointer.split(":", 1)
    path = root / artifact
    assert path.exists()
    return _pointer_value(json.loads(path.read_text(encoding="utf-8")), pointer)


def _recursive_key_present(value, key):
    if isinstance(value, dict):
        return key in value or any(_recursive_key_present(child, key) for child in value.values())
    if isinstance(value, list):
        return any(_recursive_key_present(child, key) for child in value)
    return False


def _assert_negative_witness_pointer_only(
    value,
    *,
    artifact="reports/runs/certificate-guided-constraint-training/claim_capsule.json",
):
    assert value == {
        "artifact": artifact,
        "pointer": "$.run_local.negative_witness[0]",
    }
    assert set(value) == {"artifact", "pointer"}
    assert not {"witness_id", "bedc_gap_field", "demotion_rule"} & set(value)


def _claim_gate_for_single_failed_gate(failed_name):
    claim_gate = {
        "positive_quality_improvement": True,
        "quality_q_ci95_low": 0.25,
        "required_ci95_low_gt_zero": True,
        "paired_ci_status": "pass",
        "benefit_nondecreasing": True,
        "audit_improvement_tradeoff": False,
        "classifier_shift": True,
        "positive_discovery_predicate": True,
        "matched_random_debt_also_improved": False,
        "constraint_lagrangian_beats_debt_only": True,
        "blockers": [],
    }
    if failed_name == "C1-HG2":
        claim_gate["benefit_nondecreasing"] = False
        claim_gate["blockers"] = ["benefit-decreased"]
    if failed_name == "C1-HG3":
        claim_gate["classifier_shift"] = False
        claim_gate["blockers"] = ["classifier-shift-missing"]
    if failed_name == "C1-HG4":
        claim_gate["matched_random_debt_also_improved"] = True
        claim_gate["blockers"] = ["matched-random-debt-also-improved"]
    if failed_name == "C1-HG5":
        claim_gate["constraint_lagrangian_beats_debt_only"] = False
        claim_gate["blockers"] = ["constraint-lagrangian-not-better-than-debt-only"]
    return claim_gate


def test_shared_constraint_helper_implements_relu_lagrangian():
    loss = constrained_lagrangian_loss(
        task_loss=1.0,
        uer_estimate=0.20,
        benefit_proxy=0.30,
        debt_estimate=0.60,
        thresholds=ConstraintThresholds(alpha=0.10, beta=0.50, gamma=0.40),
        lambdas=ConstraintLambdas(lambda_uer=2.0, lambda_benefit=3.0, lambda_debt=5.0),
    )

    assert loss["uer_violation"] == pytest.approx(0.10)
    assert loss["benefit_violation"] == pytest.approx(0.20)
    assert loss["debt_violation"] == pytest.approx(0.20)
    assert loss["loss"] == pytest.approx(1.0 + 2.0 * 0.10 + 3.0 * 0.20 + 5.0 * 0.20)


def test_c1_producer_runs_seven_arm_grid_and_writes_capsule(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    runner._write_payload(payload)

    loaded = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    capsule = json.loads((tmp_path / "reports/runs/fixture-c1/claim_capsule.json").read_text(encoding="utf-8"))

    assert loaded["run_id"] == "fixture-c1"
    assert loaded["source_artifacts"]["generation_script"] == "scripts/run_certificate_guided_constraint_training.py"
    assert loaded["source_artifacts"]["constraint_helper"] == "bedc_quality_lab.training.certificate_guided"
    raw_metrics = tmp_path / "reports/runs/certificate-guided-constraint-training/raw_metrics.jsonl"
    raw_records = [json.loads(line) for line in raw_metrics.read_text(encoding="utf-8").splitlines()]
    assert {record["arm"] for record in raw_records} == {
        "baseline",
        "debt_only",
        "benefit_only",
        "debt_plus_benefit",
        "constraint_lagrangian",
        "constraint_lagrangian_adaptive_lambda",
        "matched_random_debt",
    }
    assert "records" not in loaded
    assert "grid_records" not in loaded
    assert len(raw_records) == 7 * len(runner.SEEDS)
    expected_grid = 3 * 3 * 2 * 3 * 3 * 3 * len(runner.SEEDS) * 7
    expected_grid_summary = 3 * 3 * 2 * 3 * 3 * 3 * 7
    assert loaded["grid_summary"]["record_count"] == expected_grid_summary
    assert loaded["grid_record_schema"]["aggregation"] == "seed-aggregated"
    assert loaded["raw_grid_record_count"] == expected_grid
    assert loaded["raw_metrics_record_count"] == 7 * len(runner.SEEDS)
    grid_metrics = tmp_path / "reports/runs/certificate-guided-constraint-training/grid_metrics.jsonl"
    grid_summary = tmp_path / "reports/runs/certificate-guided-constraint-training/grid_summary.jsonl"
    assert len(grid_metrics.read_text(encoding="utf-8").splitlines()) == expected_grid
    assert len(grid_summary.read_text(encoding="utf-8").splitlines()) == expected_grid_summary
    first_grid_summary = json.loads(grid_summary.read_text(encoding="utf-8").splitlines()[0])
    assert first_grid_summary["aggregation"] == "seed-aggregated"
    assert first_grid_summary["seed_count"] == len(runner.SEEDS)
    assert loaded["objective"]["grid"]["seeds"] == len(runner.SEEDS)
    assert loaded["paired_seed_protocol"]["main_pair"] == ["before", "after"]
    assert loaded["arm_protocol"]["main_pair"] == ["baseline", "constraint_lagrangian"]
    assert loaded["arm_protocol"]["control_pair"] == ["baseline", "matched_random_debt"]
    assert loaded["claim_capsule"]["schema_id"] == "bedc.quality.claim_capsule"
    _assert_negative_witness_pointer_only(
        loaded["claim_capsule"]["run_local"]["negative_witness"][0],
        artifact="reports/runs/fixture-c1/claim_capsule.json",
    )
    assert set(capsule["run_local"]["negative_witness"][0]) == set(runner.NEGATIVE_WITNESS_KEYS)
    assert _pointer_value(capsule, loaded["claim_capsule"]["run_local"]["negative_witness"][0]["pointer"]) == capsule["run_local"]["negative_witness"][0]
    assert set(capsule["prior_observation"]) == {
        "source_evidence_pointer",
        "hardgate_pointer",
        "grid_summary_pointer",
        "observation",
    }
    assert capsule["source_evidence"]["grid_summary_count"] == expected_grid_summary
    assert capsule["source_evidence"]["raw_grid_record_count"] == expected_grid
    for key, value in capsule["source_evidence"].items():
        if key.endswith("_pointer"):
            assert _pointer_value(loaded, value) is not None
    for key, value in capsule["prior_observation"].items():
        if key.endswith("_pointer"):
            _assert_artifact_pointer_resolves(tmp_path, loaded, value)
    assert loaded["c2_frontier"]["axis_spec"]["projection_owner"] == "certificate-guided-constraint-training"
    assert capsule["c2_frontier"]["axis_spec"] == loaded["c2_frontier"]["axis_spec"]
    assert capsule["c2_frontier"]["hardgates"] == loaded["c2_frontier"]["hardgates"]
    assert capsule["c2_frontier"]["follow_up_training_replay"] == loaded["c2_frontier"]["follow_up_training_replay"]


def test_c1_capsule_write_is_stable_across_repeated_writes(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)

    runner._write_payload(payload)
    runner._write_payload(payload)

    canonical_payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    sidecar_payload = json.loads((tmp_path / canonical_payload["claim_capsule"]["artifact"]).read_text(encoding="utf-8"))

    assert canonical_payload["claim_capsule"] == runner._public_claim_capsule_projection(sidecar_payload)
    assert canonical_payload["claim_capsule"]["run_local"]["negative_witness"] == [
        {
            "artifact": "reports/runs/fixture-c1/claim_capsule.json",
            "pointer": "$.run_local.negative_witness[0]",
        }
    ]
    assert set(sidecar_payload["run_local"]["negative_witness"][0]) == set(runner.NEGATIVE_WITNESS_KEYS)


def test_c1_regeneration_reuses_existing_generated_at(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    capsule_path = tmp_path / runner._capsule_path("fixture-c1")
    canonical_path = tmp_path / runner.JSON_ARTIFACT
    capsule_path.parent.mkdir(parents=True, exist_ok=True)
    canonical_path.parent.mkdir(parents=True, exist_ok=True)
    capsule_path.write_text(json.dumps({"generated_at": "2035-01-02T03:04:05+00:00"}) + "\n", encoding="utf-8")
    canonical_path.write_text(json.dumps({"generated_at": "2030-01-02T03:04:05+00:00"}) + "\n", encoding="utf-8")

    assert runner._reusable_generated_at("fixture-c1") == "2035-01-02T03:04:05+00:00"

    capsule_path.unlink()

    assert runner._reusable_generated_at("fixture-c1") == "2030-01-02T03:04:05+00:00"


def test_c1_hardgates_record_tradeoff_dn_and_control(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    gates = payload["hardgate"]["gates"]

    assert gates["C1-HG1"]["status"] == "fail"
    assert gates["C1-HG1"]["failed_gate"] == "audit-improvement-tradeoff"
    assert gates["C1-HG2"]["quality_q_ci95_low"] > 0.0
    assert gates["C1-HG2"]["benefit_nondecreasing"] is False
    assert gates["C1-HG3"]["classifier_shift"] is True
    assert gates["C1-HG4"]["status"] == "pass"
    assert gates["C1-HG4"]["demote"] is False
    assert gates["C1-HG5"]["status"] == "pass"
    assert payload["claim_gate"]["constraint_lagrangian_beats_debt_only"] is True
    assert payload["claim_gate"]["matched_random_debt_also_improved"] is False
    assert payload["failed_gate"] == "audit-improvement-tradeoff"
    assert payload["verdict"] == "DN(audit-improvement-tradeoff)"
    assert payload["discovery_level"] == "DN"
    assert payload["result"]["status"] == "negative"
    assert payload["claim_capsule"]["failed_gate"] == "audit-improvement-tradeoff"
    assert "what_was_learned" in payload["claim_capsule"]


def test_c1_run_local_negative_witness_records_audit_improvement_tradeoff(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)

    assert payload["claim_capsule"]["run_local"]["negative_witness"][0] == {
        "witness_id": "certificate-guided-constraint-training:audit-improvement-tradeoff",
        "source_artifact": "reports/canonical/certificate-guided-training.json",
        "source_pointer": "$.hardgate.gates.C1-HG1.failed_gate",
        "bedc_gap_field": "Positive information gap",
        "demotion_rule": "audit-improvement-tradeoff",
        "regression_test": "tests/test_certificate_guided_constraint_training.py::test_c1_run_local_negative_witness_records_audit_improvement_tradeoff",
        "evidence_pointer": "reports/canonical/certificate-guided-training.json:$.hardgate.gates.C1-HG1",
        "status": "fail",
        "reason": "C1-HG1 records audit-improvement-tradeoff as the first failed certificate-guided constraint training hardgate",
    }


def test_c1_run_local_negative_witness_hardgates_pass_for_resolved_payload(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    run_local = payload["claim_capsule"]["run_local"]
    row = run_local["negative_witness"][0]
    hardgates = run_local["negative_witness_hardgates"]
    gates = hardgates["gates"]

    assert hardgates["status"] == "pass"
    assert hardgates["failed_gates"] == []
    assert set(gates) == {"NW-HG1", "NW-HG2", "NW-HG3", "NW-HG4"}
    assert all(gate["status"] == "pass" for gate in gates.values())

    assert gates["NW-HG1"]["evidence_pointer"] == "$.run_local.negative_witness.0"
    assert gates["NW-HG1"]["row_shape_ok"] is True
    assert gates["NW-HG1"]["list_shape_ok"] is True
    assert list(row) == list(runner.NEGATIVE_WITNESS_KEYS)

    assert gates["NW-HG2"]["evidence_pointer"] == runner.NEGATIVE_WITNESS_SOURCE_POINTER
    assert gates["NW-HG2"]["source_pointer_resolved"] is True
    assert gates["NW-HG2"]["source_pointer_value"] == "audit-improvement-tradeoff"

    evidence = runner._artifact_pointer_value(payload, runner.NEGATIVE_WITNESS_EVIDENCE_POINTER)
    assert gates["NW-HG3"]["evidence_pointer"] == runner.NEGATIVE_WITNESS_EVIDENCE_POINTER
    assert gates["NW-HG3"]["evidence_pointer_resolved"] is True
    assert evidence["status"] == "fail"
    assert evidence["failed_gate"] == "audit-improvement-tradeoff"
    assert evidence["debt_delta"] < 0
    assert evidence["benefit_delta"] < 0

    assert gates["NW-HG4"]["evidence_pointer"] == "$.run_local.negative_witness.0.status"
    assert gates["NW-HG4"]["expected_status"] == "fail"
    assert gates["NW-HG4"]["observed_status"] == "fail"


def test_c1_run_local_negative_witness_source_pointer_resolves():
    canonical_artifact = "reports/canonical/certificate-guided-training.json"
    canonical_payload = json.loads((runner.ROOT / canonical_artifact).read_text(encoding="utf-8"))
    row_ref = canonical_payload["claim_capsule"]["run_local"]["negative_witness"][0]
    row_owner = json.loads((runner.ROOT / row_ref["artifact"]).read_text(encoding="utf-8"))
    row = _pointer_value(row_owner, row_ref["pointer"])

    _assert_negative_witness_pointer_only(row_ref)
    assert row["source_artifact"] == canonical_artifact
    assert _pointer_value(canonical_payload, row["source_pointer"]) == "audit-improvement-tradeoff"


def test_c1_run_local_negative_witness_evidence_pointer_resolves():
    canonical_payload = json.loads((runner.ROOT / "reports/canonical/certificate-guided-training.json").read_text(encoding="utf-8"))
    row_ref = canonical_payload["claim_capsule"]["run_local"]["negative_witness"][0]
    row_owner = json.loads((runner.ROOT / row_ref["artifact"]).read_text(encoding="utf-8"))
    row = _pointer_value(row_owner, row_ref["pointer"])
    evidence = _artifact_pointer_value(runner.ROOT, row["evidence_pointer"])

    _assert_negative_witness_pointer_only(row_ref)
    assert evidence["status"] == "fail"
    assert evidence["failed_gate"] == "audit-improvement-tradeoff"
    assert evidence["debt_delta"] < 0
    assert evidence["benefit_delta"] < 0


def test_c1_public_surfaces_point_to_run_local_negative_witness_owner():
    for artifact in (
        "reports/canonical/certificate-guided-training.json",
        "reports/certificate_guided_training.json",
    ):
        payload = json.loads((runner.ROOT / artifact).read_text(encoding="utf-8"))
        row_ref = payload["claim_capsule"]["run_local"]["negative_witness"][0]
        owner = json.loads((runner.ROOT / row_ref["artifact"]).read_text(encoding="utf-8"))
        row = _pointer_value(owner, row_ref["pointer"])

        _assert_negative_witness_pointer_only(row_ref)
        assert set(row) == set(runner.NEGATIVE_WITNESS_KEYS)
        assert row["witness_id"] == "certificate-guided-constraint-training:audit-improvement-tradeoff"
        assert row["bedc_gap_field"] == "Positive information gap"
        assert row["demotion_rule"] == "audit-improvement-tradeoff"
        assert _pointer_value(owner, "$.run_local.negative_witness[0]") == row


def test_c1_run_local_negative_witness_regression_test_collects():
    import subprocess
    import sys

    nodeid = (
        "tests/test_certificate_guided_constraint_training.py::"
        "test_c1_run_local_negative_witness_records_audit_improvement_tradeoff"
    )
    result = subprocess.run(
        [sys.executable, "-m", "pytest", "--collect-only", "-q", nodeid],
        cwd=runner.ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert nodeid in result.stdout


def test_c1_run_local_negative_witness_fail_closed_pointer_contract(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    monkeypatch.setattr(runner, "NEGATIVE_WITNESS_SOURCE_POINTER", "$.hardgate.gates.C1-HG1.missing_cell")

    run_local = runner._negative_witness_run_local(payload)
    row = run_local["negative_witness"][0]

    assert list(row) == list(runner.NEGATIVE_WITNESS_KEYS)
    assert row["status"] == "blocked"
    assert "unresolved pointer reports/canonical/certificate-guided-training.json:$.hardgate.gates.C1-HG1.missing_cell" in row["reason"]
    assert run_local["negative_witness_hardgates"]["status"] == "fail"


def test_c1_run_local_negative_witness_no_terminal_verdict_leakage(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    run_local = payload["claim_capsule"]["run_local"]

    assert not _recursive_key_present(run_local["negative_witness"], "terminal_verdict")
    assert not _recursive_key_present(run_local["negative_witness_hardgates"], "terminal_verdict")


def test_c1_run_local_negative_witness_list_shape_only(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    negative_witness = payload["claim_capsule"]["run_local"]["negative_witness"]

    assert isinstance(negative_witness, list)
    assert isinstance(_pointer_value(payload, "$.claim_capsule.run_local.negative_witness[0]"), dict)
    assert not isinstance(negative_witness, dict)


def test_c2_frontier_reports_feasible_non_positive_cells(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    frontier = payload["c2_frontier"]
    gate = frontier["hardgates"]["gates"]["C2-HG1"]

    assert gate["status"] == "pass"
    assert gate["feasible_non_positive_count"] > 0
    witness = _pointer_value(payload, gate["first_witness_pointer"])
    assert witness["feasible"] is True
    assert witness["positive_quality_win"] is False
    assert witness["delta_quality_q"] <= 0.0 or witness["delta_benefit"] < 0.0


def test_c2_frontier_axis_hardgate_reads_resolvable_source_evidence(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    gate = payload["c2_frontier"]["hardgates"]["gates"]["C2-HG2"]

    assert gate["status"] == "pass"
    assert gate["source_pointer_count"] == gate["resolved_source_pointer_count"]
    for source in payload["c2_frontier"]["axis_spec"]["source_pointers"].values():
        assert source["artifact"] == runner.JSON_ARTIFACT
        assert _pointer_value(payload, source["pointer"]) is not None


def test_c2_frontier_replay_hardgate_reads_counts_and_pointers(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    gate = payload["c2_frontier"]["hardgates"]["gates"]["C2-HG3"]
    replay = payload["c2_frontier"]["follow_up_training_replay"]["evidence"]

    assert gate["status"] == "pass"
    assert gate["replay_counts_match"] is True
    assert replay["raw_metrics_record_count"] == _pointer_value(payload, replay["payload_raw_metrics_record_count_pointer"]["pointer"])
    assert replay["raw_grid_record_count"] == _pointer_value(payload, replay["payload_raw_grid_record_count_pointer"]["pointer"])
    assert payload["c2_frontier"]["grid_summary_record_count"] == _pointer_value(payload, replay["grid_summary_record_count_pointer"]["pointer"])


def test_c2_alias_metadata_is_non_production(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)
    capsule = payload["claim_capsule"]
    alias = capsule["c2_frontier"]["issue_alias"]
    production_text = json.dumps(
        {
            "schema_id": capsule["schema_id"],
            "run_id": capsule["run_id"],
            "producer": capsule["producer"],
            "artifact": capsule["artifact"],
            "report_artifact": capsule["report_artifact"],
            "canonical_owner": payload["c2_frontier"]["axis_spec"]["projection_owner"],
            "source_artifacts": payload["source_artifacts"],
        },
        sort_keys=True,
    )

    assert alias["production_use"] is False
    assert alias["aliases"] == [
        "certificate_constraint_frontier_v2",
        "certificate_constraint_frontier.schema.v1",
    ]
    assert capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert capsule["run_id"] == "fixture-c1"
    assert capsule["producer"] == "scripts/run_certificate_guided_constraint_training.py"
    assert "v2" not in production_text
    assert ".v1" not in production_text


@pytest.mark.parametrize(
    ("failed_name", "failed_gate"),
    [
        ("C1-HG2", "quality-q-benefit-nondecreasing"),
        ("C1-HG3", "classifier-positive-discovery-predicate"),
        ("C1-HG4", "matched-random-debt-also-improved"),
        ("C1-HG5", "constraint-lagrangian-not-better-than-debt-only"),
    ],
)
def test_c1_hardgate_aggregate_reports_independent_failed_gates(monkeypatch, tmp_path, failed_name, failed_gate):
    payload = _patched_payload(monkeypatch, tmp_path)
    claim_gate = _claim_gate_for_single_failed_gate(failed_name)
    paired_ci = payload["paired_delta_ci"]
    hardgate = runner._hardgate(payload["_records"], paired_ci, claim_gate)

    assert hardgate["gates"]["C1-HG1"]["status"] == "pass"
    assert hardgate["gates"][failed_name]["status"] == "fail"
    assert hardgate["failed_gate"] == failed_gate
    assert hardgate["failed_gates"] == [{"gate": failed_name, "failed_gate": failed_gate}]
    assert hardgate["status"] == "failed"
    assert runner._terminal_verdict(hardgate) == f"DN({failed_gate})"
    assert runner._result(payload["_records"], hardgate)["status"] == "negative"


def test_canonical_pointer_uses_c1_producer_and_compact_summary_keys():
    spec = canonical._specs_by_name()["certificate-guided-training"]
    names = {row.name for row in canonical.CANONICAL_REPORTS}
    artifacts = {row.json_artifact for row in canonical.CANONICAL_REPORTS}

    assert spec.command == ("python3", "scripts/run_certificate_guided_constraint_training.py")
    assert "grid_summary" in spec.required_json_keys
    assert "grid_metrics_artifact" in spec.required_json_keys
    assert "grid_summary_artifact" in spec.required_json_keys
    assert "records" not in spec.required_json_keys
    assert "grid_records" not in spec.required_json_keys
    assert "claim_capsule" in spec.required_json_keys
    assert "c2_frontier" in spec.required_json_keys
    assert "certificate-constraint-frontier" not in names
    assert f"reports/{'certificate'}_{'constraint'}_{'frontier'}.json" not in artifacts
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]


def test_certificate_constraint_frontier_sidecars_are_absent():
    spec_names = {row.name for row in canonical.CANONICAL_REPORTS}

    assert "certificate-constraint-frontier" not in spec_names
    assert not (runner.ROOT / "reports/certificate_constraint_frontier.json").exists()
    assert not (runner.ROOT / "reports/certificate_constraint_frontier.md").exists()


def test_committed_claim_capsule_sidecar_matches_canonical_embedding():
    canonical_artifact = "reports/canonical/certificate-guided-training.json"
    canonical_payload = json.loads((runner.ROOT / canonical_artifact).read_text(encoding="utf-8"))
    sidecar_payload = json.loads((runner.ROOT / canonical_payload["claim_capsule"]["artifact"]).read_text(encoding="utf-8"))

    assert canonical_payload["claim_capsule"] == runner._public_claim_capsule_projection(sidecar_payload)
    negative_witness_pointer = canonical_payload["claim_capsule"]["run_local"]["negative_witness"][0]
    assert negative_witness_pointer == {
        "artifact": "reports/runs/certificate-guided-constraint-training/claim_capsule.json",
        "pointer": "$.run_local.negative_witness[0]",
    }
    assert negative_witness_pointer["artifact"] == canonical_payload["claim_capsule"]["artifact"]
    pointed_payload = json.loads((runner.ROOT / negative_witness_pointer["artifact"]).read_text(encoding="utf-8"))
    row = _pointer_value(pointed_payload, negative_witness_pointer["pointer"])
    assert set(row) == set(runner.NEGATIVE_WITNESS_KEYS)
    assert row["witness_id"] == "certificate-guided-constraint-training:audit-improvement-tradeoff"
    assert row["bedc_gap_field"] == "Positive information gap"
    assert row["demotion_rule"] == "audit-improvement-tradeoff"


def test_committed_claim_capsule_source_evidence_pointers_resolve():
    canonical_artifact = "reports/canonical/certificate-guided-training.json"
    canonical_payload = json.loads((runner.ROOT / canonical_artifact).read_text(encoding="utf-8"))

    for key, value in canonical_payload["claim_capsule"]["source_evidence"].items():
        if key.endswith("_pointer"):
            assert _pointer_value(canonical_payload, value) is not None
