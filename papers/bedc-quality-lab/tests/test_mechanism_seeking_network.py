from __future__ import annotations

from copy import deepcopy
import json

import pytest

from bedc_quality_lab.mechanism_seeking_network import (
    DEFAULT_ARMS,
    DEFAULT_MECHANISMS,
    DEFAULT_SEEDS,
    DEFAULT_SHIFTS,
    DRIFT_TOLERANCE,
    DistinctionModuleEvidence,
    MSN_HARDGATES,
    MechanismSeekingNetworkProjection,
    TorchMechanismArmProtocol,
    default_grid,
)
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map
from scripts import run_mechanism_seeking_network as runner


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
    "mechanism_gate_summary",
    "gate_protocol",
    "device_protocol",
    "torch_evidence",
    "matched_random_control",
    "distinction_module_risk",
    "distinction_module_evidence",
    "hardgate",
    "failed_gate",
    "discovery_map_signal",
    "d5_m_readiness",
    "positive_claim",
    "claim_capsule_ref",
    "not_claimed",
    "what_was_learned",
    "revocation_rows",
    "forbidden_claim_term_audit",
}


def _project(records=None, **config):
    run_id = config.pop("run_id", "fixture-mechanism-seeking-network")
    artifacts = {
        "summary": f"reports/runs/{run_id}/summary.json",
        "claim_capsule": f"reports/runs/{run_id}/claim_capsule.json",
        "raw_metrics": f"reports/runs/{run_id}/raw_metrics.jsonl",
        "report": f"reports/runs/{run_id}/report.md",
    }
    full_config = {
        "run_id": run_id,
        "mechanisms": list(DEFAULT_MECHANISMS),
        "seeds": list(DEFAULT_SEEDS),
        "shifts": list(DEFAULT_SHIFTS),
        "arms": list(DEFAULT_ARMS),
        "gate_threshold": runner.DEFAULT_GATE_THRESHOLD,
        "requested_device": "mps",
        "resolved_device": "cpu",
        "torch_status": "unavailable",
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": {"torch": "fixture"},
        **config,
    }
    return MechanismSeekingNetworkProjection(
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
    assert tuple(DEFAULT_MECHANISMS) == ("copy_route", "parity_gate", "sparse_recall", "safety_boundary", "planning_route")
    assert len(default_grid()) == 135
    assert len(runner.collect_deterministic_records()) == 135


def test_deterministic_replay_and_required_keys():
    first = runner.build_projection(generated_at="fixture-time")
    second = runner.build_projection(generated_at="fixture-time")

    assert json.dumps(first["summary_payload"], sort_keys=True) == json.dumps(second["summary_payload"], sort_keys=True)
    assert REQUIRED_SUMMARY_KEYS <= set(first["summary_payload"])
    assert first["summary_payload"]["grid"]["record_count"] == 135
    assert first["summary_payload"]["grid"]["expected_record_count"] == 135
    assert first["summary_payload"]["run_artifacts"]["raw_metrics"] == first["summary_payload"]["records"]["raw_rows_pointer"]


def test_mechanism_gate_pass_and_reject_paths():
    summary = _project()["summary_payload"]

    assert summary["mechanism_gate_summary"]["accepted"] is True
    assert summary["mechanism_gate_summary"]["accepted_surface_count"] == 5
    assert summary["hardgate"]["status"] == "pass"

    records = runner.collect_deterministic_records()
    for row in records:
        if row["arm"] == "mechanism_probe":
            row["mechanism_margin"] = 0.01
            row["gate_decision"] = False
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["MSN-HG2"]["status"] == "fail"
    assert failed["discovery_map_signal"]["level_candidate"] == "DN"
    assert failed["discovery_map_signal"]["failed_gate"] == "MSN-HG2"

    two_surface_records = runner.collect_deterministic_records()
    for row in two_surface_records:
        if row["arm"] == "mechanism_probe" and row["mechanism_id"] not in {"copy_route", "parity_gate"}:
            row["mechanism_margin"] = 0.01
            row["gate_decision"] = False
    two_surface = _project(two_surface_records)["summary_payload"]
    assert two_surface["mechanism_gate_summary"]["accepted_surface_count"] == 2
    assert two_surface["mechanism_gate_summary"]["accepted"] is False
    assert two_surface["hardgate"]["gates"]["MSN-HG2"]["status"] == "fail"
    assert two_surface["hardgate"]["gates"]["MSN-HG2"]["evidence_pointer"] == "$.mechanism_gate_summary.accepted_surface_count"
    assert two_surface["discovery_map_signal"]["level_candidate"] == "DN"
    assert two_surface["discovery_map_signal"]["failed_gate"] == "MSN-HG2"


def test_torch_unavailable_boundary_records_device_without_breaking_anchor():
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps", enable_torch=False)["summary_payload"]

    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "not-requested"
    assert summary["device_protocol"]["drift_tolerance"] == pytest.approx(1.0e-4)
    assert summary["torch_evidence"]["status"] == "unavailable"
    assert summary["torch_evidence"]["row_count"] == 0
    assert summary["hardgate"]["status"] == "pass"


def test_torch_arm_protocol_records_mps_or_cpu_fields(monkeypatch):
    monkeypatch.setattr(runner, "_resolve_torch_device", lambda requested_device: ("available", "mps" if requested_device == "mps" else "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps", enable_torch=True)["summary_payload"]

    assert summary["torch_evidence"]["status"] == "available"
    assert summary["torch_evidence"]["row_count"] == 8
    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "mps"
    protocol = summary["torch_evidence"]["protocols"][0]
    assert set(protocol) == set(TorchMechanismArmProtocol.__dataclass_fields__)
    assert protocol["requested_device"] == "mps"
    assert protocol["resolved_device"] == "mps"
    assert protocol["drift_tolerance"] == pytest.approx(1.0e-4)


def test_seed_idempotence_and_quantized_tolerance():
    first = runner.deterministic_record("copy_route", 17, 0.35, "mechanism_probe")
    second = runner.deterministic_record("copy_route", 17, 0.35, "mechanism_probe")
    other = runner.deterministic_record("copy_route", 29, 0.35, "mechanism_probe")

    assert first == second
    assert abs(first["mechanism_score"] - round(first["mechanism_score"], 6)) <= DRIFT_TOLERANCE
    assert first["mechanism_score"] != other["mechanism_score"]


def test_msn_hg1_to_hg6_are_present_and_exercised():
    summary = _project()["summary_payload"]

    assert tuple(summary["hardgate"]["gates"]) == MSN_HARDGATES
    assert all(row["status"] == "pass" for row in summary["hardgate"]["gates"].values())

    missing = runner.collect_deterministic_records()[:-1]
    assert _project(missing)["summary_payload"]["hardgate"]["gates"]["MSN-HG1"]["status"] == "fail"

    weak_control = runner.collect_deterministic_records()
    for row in weak_control:
        if row["arm"] == "matched_random":
            row["mechanism_score"] = 0.3
    assert _project(weak_control)["summary_payload"]["hardgate"]["gates"]["MSN-HG3"]["status"] == "fail"

    forbidden = runner.collect_deterministic_records()
    forbidden[0]["forbidden_alias_count"] = 1
    assert _project(forbidden)["summary_payload"]["hardgate"]["gates"]["MSN-HG4"]["status"] == "fail"

    bad_torch = _project(torch_status="broken")["summary_payload"]
    assert bad_torch["hardgate"]["gates"]["MSN-HG5"]["status"] == "fail"


def test_distinction_module_evidence_has_one_record_per_mechanism():
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    evidence = summary["distinction_module_evidence"]
    allowed = set(DistinctionModuleEvidence.__dataclass_fields__)

    assert evidence["schema_id"] == "bedc-quality-lab:mechanism-seeking-network#$.distinction_module_evidence"
    assert evidence["owner_pointer"] == "$.distinction_module_evidence"
    assert [row["module_id"] for row in evidence["records"]] == list(DEFAULT_MECHANISMS)
    assert len(evidence["records"]) == 5
    assert all(set(row) == allowed for row in evidence["records"])
    assert "mechanism_score" not in json.dumps(evidence, sort_keys=True)
    assert "certificate_precision" not in json.dumps(evidence, sort_keys=True)


def test_distinction_module_evidence_pointers_resolve():
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    pointer_fields = {
        "tensor_slice_pointer",
        "classifier_surface_pointer",
        "stability_score_pointer",
        "shortcut_risk_pointer",
        "ledger_risk_pointer",
        "ablation_rows_pointer",
        "patch_rows_pointer",
    }

    for row in summary["distinction_module_evidence"]["records"]:
        for field in pointer_fields:
            assert discovery_map.pointer_value(summary, row[field]) is not None, (row["module_id"], field)


def test_surface_registry_is_pointer_only_inventory():
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    registry = summary["surface_registry"]

    assert set(registry) == set(DEFAULT_MECHANISMS) | {"forbidden_alias_audit"}
    for surface_id in DEFAULT_MECHANISMS:
        row = registry[surface_id]
        assert row["surface_id"] == surface_id
        assert row["evidence_pointer"] == f"$.mechanism_gate_summary.by_mechanism.{surface_id}"
        assert discovery_map.pointer_value(summary, row["evidence_pointer"]) is summary["mechanism_gate_summary"]["by_mechanism"][surface_id]
        assert "accepted_surface_count" not in row
        assert "accepted_count" not in row
        assert "accepted" not in row
        assert "floor" not in json.dumps(row, sort_keys=True).lower()
        assert row["default_stance"] == "bounded MSN toy mechanism surface"
    assert registry["forbidden_alias_audit"]["status"] == "pass"


def test_msn_hg6_blocks_without_ablation_or_patch_rows():
    records = runner.collect_deterministic_records()
    for row in records:
        if row["mechanism_id"] == "copy_route" and row["arm"] == "ablated_probe":
            row["ablation_row_id"] = None
        if row["mechanism_id"] == "parity_gate" and row["arm"] == "mechanism_probe":
            row["patch_row_id"] = None

    summary = _project(records)["summary_payload"]

    assert summary["hardgate"]["gates"]["MSN-HG6"]["status"] == "fail"
    assert summary["failed_gate"] == "MSN-HG6"
    assert summary["discovery_map_signal"]["level_candidate"] != "D5-M"
    assert summary["discovery_map_signal"]["failed_gate"] == "MSN-HG6"


def test_msn_hg6_allows_d5_m_readiness_only_after_risk_audit_passes():
    ready = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    assert ready["hardgate"]["gates"]["MSN-HG6"]["status"] == "pass"
    assert {row["risk_audit_status"] for row in ready["distinction_module_evidence"]["records"]} == {"pass"}
    assert ready["d5_m_readiness"]["status"] == "ready"
    assert ready["d5_m_readiness"]["passed"] is True
    assert discovery_map.pointer_value(ready, ready["d5_m_readiness"]["hardgate_pointer"]) == "pass"
    assert discovery_map.pointer_value(ready, ready["d5_m_readiness"]["d5_o_source_pointer"])

    blocked = runner.build_projection(generated_at="fixture-time", d5_o_source=None)["summary_payload"]
    assert blocked["hardgate"]["gates"]["MSN-HG6"]["status"] == "pass"
    assert blocked["d5_m_readiness"]["status"] == "blocked"
    assert blocked["d5_m_readiness"]["failed_gate"] == "d5_o_source"


def test_claim_capsule_carries_module_evidence_ref_not_copy():
    projection = runner.build_projection(generated_at="fixture-time")
    capsule = projection["claim_capsule_payload"]

    assert capsule["distinction_module_evidence_ref"] == "$.distinction_module_evidence"
    assert capsule["distinction_module_evidence"] == {
        "artifact": projection["summary_payload"]["run_artifacts"]["summary"],
        "pointer": "$.distinction_module_evidence",
    }
    serialized = json.dumps(capsule, sort_keys=True)
    assert "tensor_slice_id" not in serialized
    assert "tensor_slice_pointer" not in serialized
    assert "records" not in capsule["distinction_module_evidence"]


def test_current_lab_rejects_stale_module_evidence_pointer():
    spec = canonical._specs_by_name()["mechanism-seeking-network"]
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    summary["distinction_module_evidence"]["records"][0]["tensor_slice_pointer"] = "$.records.tensor_slice_registry.missing"

    projected = discovery_map.projection_payload(spec, summary)
    row = discovery_map.discovery_row(spec, summary, {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}})

    assert projected["main_verdict"]["mechanism_seeking_network"]["level_candidate"] == "DN"
    assert row["discovery_level"] == "DN"
    assert row["failed_gate"] == "$.distinction_module_evidence.records[0].tensor_slice_pointer"


def test_current_lab_projection_and_pointer_resolvability():
    spec = canonical._specs_by_name()["mechanism-seeking-network"]
    summary = _project()["summary_payload"]
    row = discovery_map.discovery_row(spec, summary, {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}})
    projected = discovery_map.projection_payload(spec, summary)

    assert projected["main_verdict"]["mechanism_seeking_network"]["level_candidate"] == "D4"
    assert projected["evidence_basis"]["mechanism_seeking_network"] is True
    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert discovery_map.pointer_value(summary, row["evidence_pointer"]) is not None
    assert discovery_map.pointer_value(summary, row["control_pointer"]) is not None

    failed_records = deepcopy(runner.collect_deterministic_records())
    for record in failed_records:
        if record["arm"] == "mechanism_probe":
            record["gate_decision"] = False
    failed = _project(failed_records)["summary_payload"]
    failed_row = discovery_map.discovery_row(spec, failed)
    assert failed_row["discovery_level"] == "DN"
    assert failed_row["failed_gate"] == "$.hardgate.gates.MSN-HG2.status"
    assert discovery_map.pointer_value(failed, failed_row["failed_gate"]) == "fail"


def test_current_lab_projection_rejects_msn_owner_mismatches():
    spec = canonical._specs_by_name()["mechanism-seeking-network"]
    summary = _project()["summary_payload"]

    count_mismatch = deepcopy(summary)
    count_mismatch["mechanism_gate_summary"]["accepted_surface_count"] = 4
    count_row = discovery_map.discovery_row(spec, count_mismatch)
    assert count_row["discovery_level"] == "DN"
    assert count_row["failed_gate"] == "$.mechanism_gate_summary.accepted_surface_count"

    accepted_row_mismatch = deepcopy(summary)
    accepted_row_mismatch["mechanism_gate_summary"]["by_mechanism"]["planning_route"]["accepted"] = False
    row_mismatch = discovery_map.discovery_row(spec, accepted_row_mismatch)
    assert row_mismatch["discovery_level"] == "DN"
    assert row_mismatch["failed_gate"] == "$.mechanism_gate_summary.accepted_surface_count"

    forged_positive = deepcopy(summary)
    for surface_id, row in forged_positive["mechanism_gate_summary"]["by_mechanism"].items():
        if surface_id not in {"copy_route", "parity_gate"}:
            row["accepted"] = False
    forged_positive["mechanism_gate_summary"]["accepted_surface_count"] = 2
    forged_positive["mechanism_gate_summary"]["accepted"] = False
    forged_positive["hardgate"]["gates"]["MSN-HG2"]["status"] = "fail"
    forged_positive["hardgate"]["status"] = "fail"
    forged_positive["hardgate"]["failed_gate"] = "MSN-HG2"
    forged_positive["failed_gate"] = "MSN-HG2"
    forged_positive["discovery_map_signal"]["status"] = "d4-candidate"
    forged_positive["discovery_map_signal"]["level_candidate"] = "D4"
    forged_positive["discovery_map_signal"]["failed_gate"] = None
    forged_positive["discovery_map_signal"]["failed_gate_pointer"] = None
    forged_row = discovery_map.discovery_row(spec, forged_positive)
    assert forged_row["discovery_level"] == "DN"
    assert forged_row["failed_gate"] == "$.discovery_map_signal.level_candidate"


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
    spec = canonical._specs_by_name()["mechanism-seeking-network"]

    assert spec.command == ("python3", "scripts/run_mechanism_seeking_network.py")
    assert spec.json_artifact == runner.JSON_ARTIFACT
    assert "terminal_verdict" not in spec.required_json_keys
    assert "mechanism_gate_summary" in spec.required_json_keys
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    assert ".refactor-loop/host.env" not in json.dumps(summary["source_artifacts"], sort_keys=True)
    assert "bedc_quality_lab/mechanism_seeking_network.py" in summary["source_artifacts"]["producer_sources"]
