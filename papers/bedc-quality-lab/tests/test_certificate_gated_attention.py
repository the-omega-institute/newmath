from __future__ import annotations

import inspect
import json
from copy import deepcopy

import pytest

import bedc_quality_lab.certificate_gated_attention as cga
from bedc_quality_lab.certificate_gated_attention import (
    CGA_HARDGATES,
    DEFAULT_BACKBONES,
    DEFAULT_CERTIFICATE_MODES,
    DEFAULT_SEEDS,
    DEFAULT_SURFACES,
    DRIFT_TOLERANCE,
    REQUIRED_PRODUCTION_NOT_CLAIMED,
    CertificateGatedAttentionProjection,
    TorchAttentionArmProtocol,
    default_grid,
)
from scripts import run_canonical_reports as canonical
from scripts import run_certificate_gated_attention as runner
from scripts import run_discovery_map as discovery_map


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
    "certificate_gate_summary",
    "gate_protocol",
    "arm_protocol",
    "device_protocol",
    "torch_attention_evidence",
    "matched_random_control",
    "route_patch_protocol",
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
    run_id = config.pop("run_id", "fixture-certificate-gated-attention")
    artifacts = {
        "summary": f"reports/runs/{run_id}/summary.json",
        "claim_capsule": f"reports/runs/{run_id}/claim_capsule.json",
        "raw_metrics": f"reports/runs/{run_id}/raw_metrics.jsonl",
        "report": f"reports/runs/{run_id}/report.md",
    }
    full_config = {
        "run_id": run_id,
        "surfaces": list(DEFAULT_SURFACES),
        "seeds": list(DEFAULT_SEEDS),
        "certificate_modes": list(DEFAULT_CERTIFICATE_MODES),
        "backbones": list(DEFAULT_BACKBONES),
        "requested_device": "mps",
        "resolved_device": "cpu",
        "torch_status": "unavailable",
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": {"torch": "fixture"},
        **config,
    }
    return CertificateGatedAttentionProjection(
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
    assert len(default_grid()) == 144
    assert len(runner.collect_deterministic_records()) == 144


def test_projection_uses_records_and_no_private_row_carrier():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    classes = {
        name
        for name, value in inspect.getmembers(__import__("bedc_quality_lab.certificate_gated_attention", fromlist=["x"]), inspect.isclass)
        if value.__module__ == "bedc_quality_lab.certificate_gated_attention"
    }

    assert "CertificateGatedAttentionProjection" in classes
    assert "CertificateGatedAttentionRowCarrier" not in classes
    assert "records" in payload
    assert "surface_registry" in payload
    assert all(row["backend"] == "deterministic-anchor" for row in runner.collect_deterministic_records())


def test_deterministic_replay_and_required_keys():
    first = runner.build_projection(generated_at="fixture-time")
    second = runner.build_projection(generated_at="fixture-time")

    assert json.dumps(first["summary_payload"], sort_keys=True) == json.dumps(second["summary_payload"], sort_keys=True)
    assert REQUIRED_SUMMARY_KEYS <= set(first["summary_payload"])
    assert first["summary_payload"]["grid"]["record_count"] == 144
    assert first["summary_payload"]["grid"]["expected_record_count"] == 144
    assert first["summary_payload"]["run_artifacts"]["raw_metrics"] == first["summary_payload"]["records"]["raw_rows_pointer"]


def test_certificate_gate_pass_and_reject_paths():
    summary = _project()["summary_payload"]

    assert summary["certificate_gate_summary"]["valid_gate_pass_rate"] == 1.0
    assert summary["certificate_gate_summary"]["invalid_gate_pass_rate"] == 0.0
    assert summary["certificate_gate_summary"]["gated_attention_leak_reduction_positive"] is True
    assert summary["hardgate"]["status"] == "pass"
    assert tuple(summary["hardgate"]["gates"]) == CGA_HARDGATES

    records = runner.collect_deterministic_records()
    for row in records:
        if row["backbone"] == "certificate_gated_attention" and row["certificate_mode"] == "invalid":
            row["certificate_gate_passed"] = True
    failed = _project(records)["summary_payload"]
    assert failed["hardgate"]["gates"]["CGA-HG1"]["status"] == "fail"
    assert failed["discovery_map_signal"]["level_candidate"] == "DN"


def test_cga_hg2_requires_leak_reduction():
    records = runner.collect_deterministic_records()
    for row in records:
        if row["backbone"] == "certificate_gated_attention" and row["certificate_mode"] == "valid":
            row["attention_leak"] = 0.9
    summary = _project(records)["summary_payload"]

    assert summary["hardgate"]["gates"]["CGA-HG2"]["status"] == "fail"
    assert summary["discovery_map_signal"]["failed_gate"] == "CGA-HG2"


def test_cga_hg3_requires_matched_random_separation():
    records = runner.collect_deterministic_records()
    for row in records:
        if row["backbone"] == "matched_random_gate" and row["certificate_mode"] == "valid":
            row["attention_leak"] = 0.01
    summary = _project(records)["summary_payload"]

    assert summary["matched_random_control"]["matched_random_gate_separation_positive"] is False
    assert summary["hardgate"]["gates"]["CGA-HG3"]["status"] == "fail"


def test_cga_hg4_requires_multiple_surfaces():
    records = runner.collect_deterministic_records()
    for row in records:
        if row["surface_id"] != DEFAULT_SURFACES[0] and row["backbone"] == "certificate_gated_attention":
            row["attention_leak"] = 0.9
    summary = _project(records)["summary_payload"]

    assert summary["surface_registry"]["multi_surface_positive"]["pass_surface_count"] == 1
    assert summary["hardgate"]["gates"]["CGA-HG4"]["status"] == "fail"


def test_torch_unavailable_boundary_records_device_without_breaking_anchor():
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps", enable_torch=False)["summary_payload"]

    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "not-requested"
    assert summary["torch_attention_evidence"]["status"] == "unavailable"
    assert summary["torch_attention_evidence"]["row_count"] == 0
    assert summary["hardgate"]["gates"]["CGA-HG5"]["status"] == "pass"


def test_route_patch_protocol_shape_and_pointer_resolution():
    summary = _project()["summary_payload"]
    route_patch = summary["route_patch_protocol"]

    assert set(route_patch) == {
        "valid_route_preservation",
        "invalid_route_suppression",
        "entropy_only_control",
        "classifier_shift",
        "by_surface",
        "evidence_pointer",
    }
    assert "entropy_only_control" not in summary
    assert route_patch["valid_route_preservation"]["valid_patch_delta"] > 0.0
    assert route_patch["invalid_route_suppression"]["invalid_suppression_delta"] == 1.0
    assert route_patch["entropy_only_control"]["certificate_beats_entropy_only"] is True
    assert route_patch["classifier_shift"]["classifier_shift_delta"] > 0.0
    for key in ("valid_route_preservation", "invalid_route_suppression", "entropy_only_control", "classifier_shift"):
        assert isinstance(route_patch[key], dict)
    assert set(route_patch["by_surface"]) == set(DEFAULT_SURFACES)
    for surface in route_patch["by_surface"].values():
        assert set(surface) == {
            "valid_patch_delta",
            "invalid_suppression_delta",
            "entropy_only_delta",
            "classifier_shift_count_mean",
        }
    pointer_values = [
        route_patch["valid_route_preservation"]["evidence_pointer"],
        route_patch["invalid_route_suppression"]["evidence_pointer"],
        route_patch["entropy_only_control"]["evidence_pointer"],
        route_patch["evidence_pointer"],
        summary["discovery_map_signal"]["control_pointer"],
        summary["discovery_map_signal"]["entropy_only_control_pointer"],
    ]
    assert all(discovery_map.pointer_value(summary, pointer) is not None for pointer in pointer_values)


@pytest.mark.parametrize("missing_not_claimed", REQUIRED_PRODUCTION_NOT_CLAIMED)
def test_cga_hg6_requires_production_boundary_not_claimed(monkeypatch, missing_not_claimed):
    monkeypatch.setattr(
        cga,
        "NOT_CLAIMED",
        tuple(item for item in cga.NOT_CLAIMED if item != missing_not_claimed),
    )
    summary = _project()["summary_payload"]

    assert missing_not_claimed not in summary["not_claimed"]
    assert summary["hardgate"]["gates"]["CGA-HG6"]["status"] == "fail"
    assert summary["hardgate"]["gates"]["CGA-HG6"]["evidence_pointer"] == "$.not_claimed"
    assert summary["hardgate"]["failed_gate"] == "CGA-HG6"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert summary["discovery_map_signal"]["failed_gate"] == "CGA-HG6"
    assert summary["discovery_map_signal"]["failed_gate_pointer"] == "$.hardgate.gates.CGA-HG6.status"
    assert discovery_map.pointer_value(summary, "$.hardgate.gates.CGA-HG6.status") == "fail"
    assert discovery_map.pointer_value(summary, summary["hardgate"]["gates"]["CGA-HG6"]["evidence_pointer"]) == summary["not_claimed"]


def test_torch_arm_protocol_records_mps_or_cpu_fields(monkeypatch):
    monkeypatch.setattr(runner, "_resolve_torch_device", lambda requested_device: ("available", "mps" if requested_device == "mps" else "cpu", {"torch": "fixture"}))
    summary = runner.build_projection(generated_at="fixture-time", requested_device="mps", enable_torch=True)["summary_payload"]

    assert summary["torch_attention_evidence"]["status"] == "available"
    assert summary["torch_attention_evidence"]["row_count"] == 8
    assert summary["device_protocol"]["requested_device"] == "mps"
    assert summary["device_protocol"]["resolved_device"] == "mps"
    protocol = summary["torch_attention_evidence"]["protocols"][0]
    assert set(protocol) == set(TorchAttentionArmProtocol.__dataclass_fields__)
    assert protocol["requested_device"] == "mps"
    assert protocol["resolved_device"] == "mps"


def test_cga_hg5_rejects_unexpected_torch_status():
    summary = _project(torch_status="unexpected-runtime-state")["summary_payload"]

    assert summary["torch_attention_evidence"]["status"] == "unexpected-runtime-state"
    assert summary["hardgate"]["gates"]["CGA-HG5"]["status"] == "fail"
    assert summary["hardgate"]["failed_gate"] == "CGA-HG5"
    assert summary["discovery_map_signal"]["status"] == "negative"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert summary["discovery_map_signal"]["failed_gate"] == "CGA-HG5"
    assert summary["discovery_map_signal"]["failed_gate_pointer"] == "$.hardgate.gates.CGA-HG5.status"
    assert discovery_map.pointer_value(summary, summary["discovery_map_signal"]["failed_gate_pointer"]) == "fail"


def test_forbidden_positive_claim_term_demotes_claim(monkeypatch):
    forbidden_claim = {
        "text": "Certificate-gated attention is not a global-quality result.",
        "scope": "deterministic anchor grid with bounded optional PyTorch evidence",
    }
    monkeypatch.setattr(cga, "POSITIVE_CLAIM", forbidden_claim)
    projected = _project()
    summary = projected["summary_payload"]
    capsule = projected["claim_capsule_payload"]

    assert summary["forbidden_claim_term_audit"]["status"] == "fail"
    assert summary["forbidden_claim_term_audit"]["hits"] == ["global-quality"]
    assert summary["claim_capsule_status"] == "failed"
    assert summary["failed_gate"] == "forbidden-positive-claim-term"
    assert summary["hardgate"]["gates"]["forbidden-positive-claim-term"]["status"] == "fail"
    assert summary["discovery_map_signal"]["status"] == "negative"
    assert summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert summary["discovery_map_signal"]["reason"] == "forbidden-positive-claim-term"
    assert summary["discovery_map_signal"]["failed_gate"] == "forbidden-positive-claim-term"
    assert summary["discovery_map_signal"]["failed_gate_pointer"] == "$.forbidden_claim_term_audit.status"
    assert discovery_map.pointer_value(summary, summary["discovery_map_signal"]["failed_gate_pointer"]) == "fail"
    assert capsule["claim_status"] == "failed"
    assert capsule["failed_gate"] == "forbidden-positive-claim-term"


def test_seed_idempotence_and_quantized_tolerance():
    first = runner.deterministic_record("copy_binding", 13, "valid", "certificate_gated_attention")
    second = runner.deterministic_record("copy_binding", 13, "valid", "certificate_gated_attention")
    other = runner.deterministic_record("copy_binding", 29, "valid", "certificate_gated_attention")

    assert first == second
    assert abs(first["attention_leak"] - round(first["attention_leak"], 6)) <= DRIFT_TOLERANCE
    assert first["attention_leak"] != other["attention_leak"]


def test_current_lab_projection_and_pointer_resolvability():
    spec = canonical._specs_by_name()["certificate-gated-attention"]
    summary = _project()["summary_payload"]
    row = discovery_map.discovery_row(spec, summary, {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}})
    projected = discovery_map.projection_payload(spec, summary)

    assert projected["main_verdict"]["certificate_gated_attention"]["level_candidate"] == "D4"
    assert projected["evidence_basis"]["certificate_gated_attention"] is True
    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert discovery_map.pointer_value(summary, row["evidence_pointer"]) is not None
    assert discovery_map.pointer_value(summary, row["control_pointer"]) is not None
    assert row["control_pointer"] == "$.route_patch_protocol"

    failed_records = deepcopy(runner.collect_deterministic_records())
    for record in failed_records:
        if record["backbone"] == "certificate_gated_attention" and record["certificate_mode"] == "valid":
            record["attention_leak"] = 0.9
    failed = _project(failed_records)["summary_payload"]
    failed_row = discovery_map.discovery_row(spec, failed)
    assert failed_row["discovery_level"] == "DN"
    assert failed_row["failed_gate"] == "$.hardgate.gates.CGA-HG2.status"
    assert discovery_map.pointer_value(failed, failed_row["failed_gate"]) == "fail"


@pytest.mark.parametrize(
    ("mutation", "failed_gate"),
    (
        (lambda payload: payload.pop("route_patch_protocol"), "$.route_patch_protocol"),
        (lambda payload: payload["hardgate"]["gates"].pop("CGA-HG6"), "$.hardgate.gates.CGA-HG6.status"),
        (
            lambda payload: (
                payload.__setitem__("entropy_only_control", payload["route_patch_protocol"]["entropy_only_control"]),
                payload["discovery_map_signal"].__setitem__("control_pointer", "$.entropy_only_control"),
            ),
            "$.discovery_map_signal.control_pointer",
        ),
        (lambda payload: payload.pop("not_claimed"), "$.not_claimed"),
        (lambda payload: payload.__setitem__("not_claimed", {"claims": []}), "$.not_claimed"),
        (
            lambda payload: payload["not_claimed"].remove(REQUIRED_PRODUCTION_NOT_CLAIMED[0]),
            "$.not_claimed",
        ),
        (
            lambda payload: payload["hardgate"]["gates"]["CGA-HG6"].__setitem__("evidence_pointer", "$.hardgate.gates.CGA-HG6.status"),
            "$.hardgate.gates.CGA-HG6.evidence_pointer",
        ),
    ),
)
def test_current_lab_cga_stale_payloads_fail_closed(mutation, failed_gate):
    spec = canonical._specs_by_name()["certificate-gated-attention"]
    payload = _project()["summary_payload"]
    mutation(payload)

    projected = discovery_map.projection_payload(spec, payload)
    row = discovery_map.discovery_row(spec, payload)

    assert projected["main_verdict"]["certificate_gated_attention"] == {
        "level_candidate": "DN",
        "status": "negative",
    }
    assert row["discovery_level"] == "DN"
    assert row["audit_status"] == "invalid"
    assert row["failed_gate"] == failed_gate


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
    spec = canonical._specs_by_name()["certificate-gated-attention"]

    assert spec.command == ("python3", "scripts/run_certificate_gated_attention.py")
    assert spec.json_artifact == runner.JSON_ARTIFACT
    assert "terminal_verdict" not in spec.required_json_keys
    assert "schema_id" in spec.required_json_keys
    summary = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    assert ".refactor-loop/host.env" not in json.dumps(summary["source_artifacts"], sort_keys=True)
    assert "bedc_quality_lab/certificate_gated_attention.py" in summary["source_artifacts"]["producer_sources"]
