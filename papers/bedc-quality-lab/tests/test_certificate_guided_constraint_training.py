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
        assert isinstance(cursor, dict)
        assert part in cursor
        cursor = cursor[part]
    return cursor


def _assert_artifact_pointer_resolves(root, payload, artifact_pointer):
    artifact, pointer = artifact_pointer.split(":", 1)
    path = root / artifact
    assert path.exists()
    pointed_payload = json.loads(path.read_text(encoding="utf-8"))
    assert _pointer_value(pointed_payload, pointer) is not None


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
    assert capsule == loaded["claim_capsule"]
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


def test_c1_capsule_write_is_stable_across_repeated_writes(monkeypatch, tmp_path):
    payload = _patched_payload(monkeypatch, tmp_path)

    runner._write_payload(payload)
    runner._write_payload(payload)

    canonical_payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    sidecar_payload = json.loads((tmp_path / canonical_payload["claim_capsule"]["artifact"]).read_text(encoding="utf-8"))

    assert canonical_payload["claim_capsule"] == sidecar_payload


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
    assert "certificate-constraint-frontier" not in names
    assert f"reports/{'certificate'}_{'constraint'}_{'frontier'}.json" not in artifacts
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]


def test_committed_claim_capsule_sidecar_matches_canonical_embedding():
    canonical_artifact = "reports/canonical/certificate-guided-training.json"
    canonical_payload = json.loads((runner.ROOT / canonical_artifact).read_text(encoding="utf-8"))
    sidecar_payload = json.loads((runner.ROOT / canonical_payload["claim_capsule"]["artifact"]).read_text(encoding="utf-8"))

    assert canonical_payload["claim_capsule"] == sidecar_payload


def test_committed_claim_capsule_source_evidence_pointers_resolve():
    canonical_artifact = "reports/canonical/certificate-guided-training.json"
    canonical_payload = json.loads((runner.ROOT / canonical_artifact).read_text(encoding="utf-8"))

    for key, value in canonical_payload["claim_capsule"]["source_evidence"].items():
        if key.endswith("_pointer"):
            assert _pointer_value(canonical_payload, value) is not None
