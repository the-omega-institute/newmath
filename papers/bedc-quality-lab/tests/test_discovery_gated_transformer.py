import json

import pytest

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.discovery_gated_transformer import (
    ARTIFACT_ID,
    CANONICAL_JSON_ARTIFACT,
    TOOL_ROUTE_CGA_ROUTE_PATCH_REF,
    TOOL_ROUTE_REQUIRED_KEYS,
    TOOL_ROUTE_SCHEMA_ID,
    GATE_NAMES,
    MODEL_ID,
    SCHEMA_ID,
    build_projection,
    evaluate_dgt_tool_route_hardgates,
    default_component_refs,
    validate_projection,
    validate_dgt_tool_route_evidence,
)
from scripts import run_discovery_gated_transformer as dgt


def _walk(value):
    if isinstance(value, dict):
        yield value
        for item in value.values():
            yield from _walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from _walk(item)


def test_dgt_has_twenty_gate_names():
    payload = dgt.build_payload(generated_at="fixture-time")

    assert GATE_NAMES == tuple(f"DGT-HG{index}" for index in range(1, 21))
    assert payload["hardgate"]["gate_names"] == [f"DGT-HG{index}" for index in range(1, 21)]
    assert list(payload["hardgate"]["gates"]) == [f"DGT-HG{index}" for index in range(1, 21)]


def test_dgt_missing_pointer_fails_closed():
    refs = default_component_refs()
    refs.pop("discovery_map")

    payload = build_projection(generated_at="fixture-time", component_refs=refs)

    assert payload["hardgate"]["status"] == "fail"
    assert {row["status"] for row in payload["hardgate"]["gates"].values()} == {"fail"}


def test_dgt_complete_fixture_is_d4_candidate():
    payload = dgt.build_payload(generated_at="fixture-time")

    assert payload["schema_id"] == SCHEMA_ID
    assert payload["artifact_id"] == ARTIFACT_ID
    assert payload["model_id"] == MODEL_ID
    assert payload["hardgate"]["status"] == "pass"
    assert payload["tool_route_evidence"]["hardgate"]["status"] == "pass"
    assert payload["discovery_map_signal"]["level_candidate"] == "D4"
    assert payload["discovery_map_signal"]["status"] == "candidate-local-positive"


def test_dgt_component_evidence_is_pointer_only():
    payload = dgt.build_payload(generated_at="fixture-time")

    for cell in payload["component_refs"].values():
        assert set(cell) == {"artifact", "pointer"}
        assert cell["pointer"].startswith("$")
    serialized = json.dumps(payload, sort_keys=True)
    for forbidden in (
        '"records"',
        '"quality_q"',
        '"attention_rows"',
        '"search_score"',
        '"terminal_verdict"',
        '"standalone_verdict"',
        '"private_row_carrier"',
    ):
        assert forbidden not in serialized


def test_dgt_artifact_ids_are_unversioned():
    payload = dgt.build_payload(generated_at="fixture-time")
    serialized = json.dumps(payload, sort_keys=True)

    assert payload["schema_id"] == "bedc-quality-lab:discovery-gated-transformer"
    assert payload["artifact_id"] == "bedc-quality-lab:discovery-gated-transformer"
    assert payload["model_id"] == "discovery-gated-transformer"
    assert "v0" not in serialized.lower()
    assert "v1" not in serialized.lower()


def test_dgt_explicitly_denies_global_superiority_and_production_authority():
    payload = dgt.build_payload(generated_at="fixture-time")
    nonclaims = " ".join(payload["not_claimed"]).lower()

    assert "global superiority" in nonclaims
    assert "production authority" in nonclaims


def test_dgt_rejects_inline_source_metric_bodies():
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutated["component_refs"]["metric_body"] = {"artifact": "x", "pointer": "$", "records": []}

    with pytest.raises(ValueError, match="inline source body"):
        validate_projection(mutated)


def test_dgt_written_sidecars_resolve(tmp_path):
    payload = dgt.build_payload(generated_at="fixture-time")
    dgt.write_artifacts(payload, root=tmp_path)

    assert resolve_artifact_pointer(tmp_path, f"{CANONICAL_JSON_ARTIFACT}:$") is not None
    for key in (
        "claim_capsule_ref",
        "evidence_envelope_ref",
        "mechanism_namecert_ref",
        "jet_certificate_ref",
    ):
        cell = payload[key]
        sidecar = resolve_artifact_pointer(tmp_path, f"{cell['artifact']}:{cell['pointer']}")
        assert sidecar is not None
        assert sidecar["model_id"] == "discovery-gated-transformer"


def test_dgt_canonical_payload_does_not_inline_sidecars():
    payload = dgt.build_payload(generated_at="fixture-time")
    sidecars = dgt.build_run_sidecars(generated_at="fixture-time")
    serialized = json.dumps(payload, sort_keys=True)

    for sidecar in sidecars.values():
        assert json.dumps(sidecar, sort_keys=True) not in serialized


def test_tool_route_schema_required_keys_and_pointers_resolve(tmp_path):
    payload = dgt.build_payload(generated_at="fixture-time")
    dgt.write_artifacts(payload, root=tmp_path)
    tool_route = payload["tool_route_evidence"]

    assert tuple(tool_route) == TOOL_ROUTE_REQUIRED_KEYS
    assert tool_route["schema_id"] == TOOL_ROUTE_SCHEMA_ID
    assert tool_route["owner_ref"] == f"{CANONICAL_JSON_ARTIFACT}:$"
    assert tool_route["cga_route_patch_ref"] == TOOL_ROUTE_CGA_ROUTE_PATCH_REF
    for pointer in (
        tool_route["owner_ref"],
        f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence",
        f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.hardgate",
        f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.synthetic_tool_call_grid[0]",
    ):
        assert resolve_artifact_pointer(tmp_path, pointer) is not None


def test_invalid_and_unsafe_routes_are_blocked_not_admitted():
    payload = dgt.build_payload(generated_at="fixture-time")
    tool_route = payload["tool_route_evidence"]
    blocked_ids = {row["route_id"] for row in tool_route["blocked_route_evidence"]["rows"]}
    admitted_ids = {row["route_id"] for row in tool_route["admission_ledger"]["rows"]}
    invalid_unsafe_ids = {
        row["route_id"]
        for row in tool_route["synthetic_tool_call_grid"]
        if row["route_class"] in {"invalid_route", "unsafe_route"}
    }

    assert invalid_unsafe_ids == blocked_ids
    assert invalid_unsafe_ids.isdisjoint(admitted_ids)


def test_dgt_tool_hg2_requires_cga_route_patch_pointer_no_copy():
    payload = dgt.build_payload(generated_at="fixture-time")
    tool_route = json.loads(json.dumps(payload["tool_route_evidence"]))

    tool_route["cga_route_patch_ref"] = "reports/canonical/certificate-gated-attention.json:$"
    hardgate = evaluate_dgt_tool_route_hardgates(tool_route)
    assert hardgate["gates"]["DGT-TOOL-HG2"]["status"] == "fail"
    with pytest.raises(ValueError, match="hardgate"):
        validate_dgt_tool_route_evidence(tool_route)

    copied = json.loads(json.dumps(payload["tool_route_evidence"]))
    copied["cga_metric_body"] = {"classifier_payload": {"rows": []}}
    hardgate = evaluate_dgt_tool_route_hardgates(copied)
    assert hardgate["gates"]["DGT-TOOL-HG2"]["status"] == "fail"


def test_dgt_tool_hg3_fails_when_invalid_or_unsafe_route_is_ledgered():
    payload = dgt.build_payload(generated_at="fixture-time")
    tool_route = json.loads(json.dumps(payload["tool_route_evidence"]))
    blocked_route = tool_route["blocked_route_evidence"]["rows"][0]
    tool_route["admission_ledger"]["rows"].append(
        {
            "route_id": blocked_route["route_id"],
            "route_class": blocked_route["route_class"],
            "admission_basis_ref": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.synthetic_tool_call_grid[2]",
        }
    )

    hardgate = evaluate_dgt_tool_route_hardgates(tool_route)
    assert hardgate["gates"]["DGT-TOOL-HG3"]["status"] == "fail"
    with pytest.raises(ValueError, match="hardgate"):
        validate_dgt_tool_route_evidence(tool_route)


def test_positive_signal_requires_classifier_surface_delta_and_net_positive_signal():
    payload = dgt.build_payload(generated_at="fixture-time")
    tool_route = json.loads(json.dumps(payload["tool_route_evidence"]))
    tool_route["synthetic_tool_call_grid"][0]["classifier_surface_delta"] = None
    hardgate = evaluate_dgt_tool_route_hardgates(tool_route)
    assert hardgate["gates"]["DGT-TOOL-HG1"]["status"] == "fail"

    tool_route = json.loads(json.dumps(payload["tool_route_evidence"]))
    tool_route["synthetic_tool_call_grid"][0]["net_positive_signal"] = False
    hardgate = evaluate_dgt_tool_route_hardgates(tool_route)
    assert hardgate["gates"]["DGT-TOOL-HG1"]["status"] == "fail"


def test_hg6_rejects_refactor_loop_terminal_verdict_and_alias_refs():
    payload = dgt.build_payload(generated_at="fixture-time")
    for forbidden in (
        ".refactor-loop/host.env",
        "terminal_verdict",
        "reports/canonical/discovery_gated_transformer.json",
        "reports/canonical/tool-use-dgt.json",
        "reports/canonical/tool-use-toy-dgt.json",
    ):
        tool_route = json.loads(json.dumps(payload["tool_route_evidence"]))
        tool_route["forbidden_alias_audit"]["forbidden_refs"] = [forbidden]
        hardgate = evaluate_dgt_tool_route_hardgates(tool_route)
        assert hardgate["gates"]["DGT-TOOL-HG6"]["status"] == "fail"
