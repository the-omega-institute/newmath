from __future__ import annotations

import json
from copy import deepcopy

import pytest

from bedc_quality_lab.discovery_regularized_training import (
    DEFAULT_ARMS,
    DEFAULT_DISCOVERY_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    DRIFT_TOLERANCE,
    DiscoveryRegularizedTrainingProjection,
    TorchTrainingArmProtocol,
    default_grid,
)
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map
from scripts import run_discovery_regularized_training as runner


REQUIRED_SUMMARY_KEYS = {
    "schema_id",
    "artifact_id",
    "generated_at",
    "run_id",
    "producer",
    "projector",
    "run_artifacts",
    "source_artifacts",
    "config",
    "grid",
    "records",
    "surface_registry",
    "lambda_summary",
    "constraint_summary",
    "arm_protocol",
    "device_protocol",
    "torch_training_evidence",
    "matched_random_control",
    "hardgate",
    "failed_gate",
    "discovery_map_signal",
    "positive_claim",
    "claim_capsule_ref",
    "not_claimed",
    "what_was_learned",
    "revocation_rows",
    "forbidden_claim_term_audit",
}


def _project(records=None, **config):
    run_id = config.pop("run_id", "fixture-discovery-regularized-training")
    artifacts = {
        "summary": f"reports/runs/{run_id}/summary.json",
        "claim_capsule": f"reports/runs/{run_id}/claim_capsule.json",
        "raw_metrics": f"reports/runs/{run_id}/raw_metrics.jsonl",
        "report": f"reports/runs/{run_id}/report.md",
    }
    full_config = {
        "run_id": run_id,
        "discovery_lambdas": list(DEFAULT_DISCOVERY_LAMBDAS),
        "rhos": list(DEFAULT_RHOS),
        "mixings": list(DEFAULT_MIXINGS),
        "seeds": list(DEFAULT_SEEDS),
        "arms": list(DEFAULT_ARMS),
        "requested_device": "mps",
        "resolved_device": "cpu",
        "torch_status": "unavailable",
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": {"torch": "fixture"},
        **config,
    }
    return DiscoveryRegularizedTrainingProjection(
        config=full_config,
        records=runner.collect_deterministic_records() if records is None else records,
        generated_at="fixture-time",
        run_artifacts=artifacts,
    ).project()


def _recursive_keys(value):
    if isinstance(value, dict):
        keys = set(value)
        for item in value.values():
            keys.update(_recursive_keys(item))
        return keys
    if isinstance(value, list):
        keys = set()
        for item in value:
            keys.update(_recursive_keys(item))
        return keys
    return set()


def _recursive_pointer_fields(value, path="$"):
    if isinstance(value, dict):
        found = []
        for key, item in value.items():
            child_path = f"{path}.{key}"
            if isinstance(key, str) and key.endswith("_pointer"):
                found.append((child_path, item))
            found.extend(_recursive_pointer_fields(item, child_path))
        return found
    if isinstance(value, list):
        found = []
        for index, item in enumerate(value):
            found.extend(_recursive_pointer_fields(item, f"{path}.{index}"))
        return found
    return []


def test_default_deterministic_grid_has_expected_anchor_size():
    assert len(default_grid()) == 720
    assert len(runner.collect_deterministic_records()) == 720


def test_deterministic_replay_and_required_keys():
    first = runner.build_projection(generated_at="fixture-time")
    second = runner.build_projection(generated_at="fixture-time")

    assert json.dumps(first["summary_payload"], sort_keys=True) == json.dumps(second["summary_payload"], sort_keys=True)
    assert REQUIRED_SUMMARY_KEYS <= set(first["summary_payload"])
    assert first["summary_payload"]["grid"]["record_count"] == 720
    assert first["summary_payload"]["grid"]["expected_record_count"] == 720
    assert first["summary_payload"]["run_artifacts"]["raw_metrics"] == first["summary_payload"]["records"]["raw_rows_pointer"]


def test_torch_unavailable_boundary_records_device_without_breaking_anchor():
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps", enable_torch=False)["summary_payload"]

    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "not-requested"
    assert summary["device_protocol"]["drift_tolerance"] == pytest.approx(1.0e-4)
    assert summary["torch_training_evidence"]["status"] == "unavailable"
    assert summary["torch_training_evidence"]["row_count"] == 0
    assert summary["hardgate"]["status"] == "pass"


def test_torch_arm_protocol_records_mps_or_cpu_fields(monkeypatch):
    monkeypatch.setattr(runner, "_resolve_torch_device", lambda requested_device: ("available", "mps" if requested_device == "mps" else "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps", enable_torch=True)["summary_payload"]

    assert summary["torch_training_evidence"]["status"] == "available"
    assert summary["torch_training_evidence"]["row_count"] == 16
    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "mps"
    protocol = summary["torch_training_evidence"]["protocols"][0]
    assert set(protocol) == set(TorchTrainingArmProtocol.__dataclass_fields__)
    assert protocol["requested_device"] == "mps"
    assert protocol["resolved_device"] == "mps"
    assert protocol["drift_tolerance"] == pytest.approx(1.0e-4)


def test_seed_idempotence_and_quantized_tolerance():
    first = runner.deterministic_record(0.001, 0.9, "spiral", 11, "drt")
    second = runner.deterministic_record(0.001, 0.9, "spiral", 11, "drt")
    other = runner.deterministic_record(0.001, 0.9, "spiral", 23, "drt")

    assert first == second
    assert abs(first["quality_q"] - round(first["quality_q"], 6)) <= DRIFT_TOLERANCE
    assert first["quality_q"] != other["quality_q"]


def test_drt_hg1_debt_down_benefit_down_demotes():
    records = runner.collect_deterministic_records()
    for row in records:
        if row["arm"] == "drt":
            row["benefit_q"] = 0.1
    summary = _project(records)["summary_payload"]

    assert summary["hardgate"]["gates"]["DRT-HG1"]["status"] == "fail"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert summary["discovery_map_signal"]["failed_gate"] == "DRT-HG1"


def test_drt_hg2_requires_positive_ci_low_and_benefit_nondecreasing():
    summary = _project()["summary_payload"]
    assert summary["lambda_summary"]["delta_quality_ci_low_positive"] is True
    assert summary["lambda_summary"]["benefit_nondecreasing"] is True
    assert summary["hardgate"]["gates"]["DRT-HG2"]["status"] == "pass"

    records = runner.collect_deterministic_records()
    for row in records:
        if row["arm"] == "drt":
            row["delta_quality_ci_low"] = -0.001
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRT-HG2"]["status"] == "fail"
    assert failed["discovery_map_signal"]["failed_gate"] == "DRT-HG2"


def test_drt_hg3_classifier_shift_and_net_positive_signal():
    summary = _project()["summary_payload"]
    assert summary["surface_registry"]["classifier_shift"]["classifier_shift_positive"] is True
    assert summary["surface_registry"]["classifier_shift"]["net_positive_signal"] is True
    assert summary["hardgate"]["gates"]["DRT-HG3"]["status"] == "pass"

    records = runner.collect_deterministic_records()
    for row in records:
        if row["arm"] == "drt":
            row["classifier_shift_count"] = 0
            row["net_positive_signal"] = False
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["DRT-HG3"]["status"] == "fail"


def test_drt_hg4_matched_random_certificate_loss_improvement_demotion():
    records = runner.collect_deterministic_records()
    for row in records:
        if row["arm"] == "matched_random":
            row["certificate_loss"] = 0.01
    summary = _project(records)["summary_payload"]

    assert summary["matched_random_control"]["certificate_loss_improvement"] is False
    assert summary["hardgate"]["gates"]["DRT-HG4"]["status"] == "fail"
    assert summary["discovery_map_signal"]["failed_gate"] == "DRT-HG4"


def test_drt_hg5_rejects_task_accuracy_only_rows():
    records = runner.collect_deterministic_records()
    for row in records:
        if row["arm"] == "task_only":
            row["net_positive_signal"] = True
            break
    summary = _project(records)["summary_payload"]

    assert summary["surface_registry"]["task_accuracy_only"]["task_accuracy_only_rejected"] is False
    assert summary["hardgate"]["gates"]["DRT-HG5"]["status"] == "fail"
    assert summary["discovery_map_signal"]["failed_gate"] == "DRT-HG5"


def test_current_lab_projection_and_pointer_resolvability():
    spec = canonical._specs_by_name()["discovery-regularized-training"]
    summary = _project()["summary_payload"]
    row = discovery_map.discovery_row(spec, summary, {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}})
    projected = discovery_map.projection_payload(spec, summary)

    assert projected["main_verdict"]["discovery_regularized_training"]["level_candidate"] == "D4"
    assert projected["evidence_basis"]["discovery_regularized_training"] is True
    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert discovery_map.pointer_value(summary, row["evidence_pointer"]) is not None
    assert discovery_map.pointer_value(summary, row["control_pointer"]) is not None

    failed_records = deepcopy(runner.collect_deterministic_records())
    for record in failed_records:
        if record["arm"] == "drt":
            record["classifier_shift_count"] = 0
            record["net_positive_signal"] = False
    failed = _project(failed_records)["summary_payload"]
    failed_row = discovery_map.discovery_row(spec, failed)
    assert failed_row["discovery_level"] == "DN"
    assert failed_row["failed_gate"] == "$.hardgate.gates.DRT-HG3.status"
    assert discovery_map.pointer_value(failed, failed_row["failed_gate"]) == "fail"


def test_recursive_no_terminal_verdict_and_pointer_fields_resolve(tmp_path):
    projection = runner.build_projection(run_id="fixture-canonical", generated_at="fixture-time")
    runner.write_artifacts(projection, root=tmp_path)
    summary = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    capsule = json.loads((tmp_path / summary["run_artifacts"]["claim_capsule"]).read_text(encoding="utf-8"))

    assert "terminal_verdict" not in _recursive_keys({"summary": summary, "capsule": capsule})
    dangling = [
        (path, pointer)
        for path, pointer in _recursive_pointer_fields(summary)
        if isinstance(pointer, str)
        and pointer.startswith("$.")
        and discovery_map.pointer_value(summary, pointer) is None
    ]
    assert dangling == []
    assert summary["claim_capsule_ref"] == summary["run_artifacts"]["claim_capsule"]
    assert summary["not_claimed"] == capsule["not_claimed"]


def test_canonical_spec_uses_committed_config_and_source_artifacts():
    spec = canonical._specs_by_name()["discovery-regularized-training"]

    assert spec.command == ("python3", "scripts/run_discovery_regularized_training.py")
    assert spec.json_artifact == runner.JSON_ARTIFACT
    assert "terminal_verdict" not in spec.required_json_keys
    assert "schema_id" in spec.required_json_keys
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    assert ".refactor-loop/host.env" not in json.dumps(summary["source_artifacts"], sort_keys=True)
    assert "bedc_quality_lab/discovery_regularized_training.py" in summary["source_artifacts"]["producer_sources"]
