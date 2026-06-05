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
    assert len(default_grid()) == 81
    assert len(runner.collect_deterministic_records()) == 81


def test_deterministic_replay_and_required_keys():
    first = runner.build_projection(generated_at="fixture-time")
    second = runner.build_projection(generated_at="fixture-time")

    assert json.dumps(first["summary_payload"], sort_keys=True) == json.dumps(second["summary_payload"], sort_keys=True)
    assert REQUIRED_SUMMARY_KEYS <= set(first["summary_payload"])
    assert first["summary_payload"]["grid"]["record_count"] == 81
    assert first["summary_payload"]["grid"]["expected_record_count"] == 81
    assert first["summary_payload"]["run_artifacts"]["raw_metrics"] == first["summary_payload"]["records"]["raw_rows_pointer"]


def test_mechanism_gate_pass_and_reject_paths():
    summary = _project()["summary_payload"]

    assert summary["mechanism_gate_summary"]["accepted"] is True
    assert summary["mechanism_gate_summary"]["accepted_surface_count"] >= 2
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


def test_msn_hg1_to_hg5_are_present_and_exercised():
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
