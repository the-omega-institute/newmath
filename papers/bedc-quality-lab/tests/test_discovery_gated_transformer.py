import json

import pytest

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.discovery_gated_transformer import (
    ARTIFACT_ID,
    CANONICAL_JSON_ARTIFACT,
    TOOL_ROUTE_CGA_ROUTE_PATCH_REF,
    TOOL_ROUTE_REQUIRED_KEYS,
    TOOL_ROUTE_SCHEMA_ID,
    D4_PROJECTION_GATE_NAMES,
    FAMILY_DEFINITION_POINTER,
    FAMILY_DEFINITION_REQUIRED_KEYS,
    GATE_NAMES,
    JET_CERTIFICATE_SCHEMA_ID,
    JET_HARDGATE_NAMES,
    JET_REQUIRED_SURFACES,
    JET_SURFACE_SLOTS,
    MODEL_ID,
    SCHEMA_ID,
    build_dgt_jet_certificate,
    build_d4_projection_payload,
    build_projection,
    evaluate_dgt_family_definition_hardgate,
    evaluate_dgt_jet_hardgates,
    evaluate_dgt_tool_route_hardgates,
    default_component_refs,
    default_dgt_source_refs,
    validate_projection,
    validate_dgt_hardgate_evidence_bundle,
    validate_dgt_family_definition,
    validate_dgt_jet_certificate,
    validate_dgt_tool_route_evidence,
    validate_d4_projection,
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


def _write_required_dgt_external_artifacts(root):
    path = root / "reports" / "canonical" / "discovery-gated-nas.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"candidate_protocol": {"design_search_certificate": {"slot_state": "present-but-fail-closed"}}})
        + "\n",
        encoding="utf-8",
    )


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
    assert payload["discovery_map_signal"]["evidence"] == {
        "artifact": CANONICAL_JSON_ARTIFACT,
        "pointer": "$.d4_projection.discovery_level",
    }
    assert tuple(payload["d4_projection"]["gates"]) == D4_PROJECTION_GATE_NAMES
    assert payload["d4_projection"]["discovery_level"] == "D4"
    assert payload["d4_projection"]["readiness"] == "ready"
    assert payload["d4_projection"]["failed_gate"] is None


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


def test_dgt_d4_projection_fails_closed_when_proj_gate_fails():
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutated["tool_route_evidence"]["net_positive_signal"] = False
    projection = build_d4_projection_payload(mutated, payload["d4_projection"]["core_contracts"])

    assert projection["gates"]["PROJ-HG3"]["status"] == "fail"
    assert projection["discovery_level"] == "D0"
    assert projection["readiness"] == "blocked"
    assert projection["failed_gate"] == "PROJ-HG3"
    assert validate_d4_projection(projection, mutated) == []


def test_dgt_d4_projection_rejects_terminal_verdict_surface():
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload["d4_projection"]))
    mutated["claim_basis"]["terminal_verdict"] = "accepted_positive_discovery"

    assert "forbidden authority token" in "; ".join(validate_d4_projection(mutated, payload))


def test_dgt_artifact_ids_are_unversioned():
    payload = dgt.build_payload(generated_at="fixture-time")
    serialized = json.dumps(payload, sort_keys=True)

    assert payload["schema_id"] == "bedc-quality-lab:discovery-gated-transformer"
    assert payload["artifact_id"] == "bedc-quality-lab:discovery-gated-transformer"
    assert payload["model_id"] == "discovery-gated-transformer"
    assert "v0" not in serialized.lower()
    assert "v1" not in serialized.lower()


def test_dgt_not_claimed_excludes_forbidden_positive_claim_wording():
    payload = dgt.build_payload(generated_at="fixture-time")
    nonclaims = " ".join(payload["not_claimed"]).lower()

    assert "global superiority" not in nonclaims
    assert "production" not in nonclaims
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"


def test_dgt_rejects_inline_source_metric_bodies():
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutated["component_refs"]["metric_body"] = {"artifact": "x", "pointer": "$", "records": []}

    with pytest.raises(ValueError, match="inline source body"):
        validate_projection(mutated)


def test_dgt_written_sidecars_resolve(tmp_path):
    _write_required_dgt_external_artifacts(tmp_path)
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
    source_refs = resolve_artifact_pointer(tmp_path, "reports/runs/discovery-gated-transformer/source_refs.json:$")
    assert source_refs["source_refs"]["boundary_spec"]["pointer"].startswith("$")
    assert payload["hardgate"]["gates"]["DGT-HG18"]["evidence"] == {
        "artifact": "reports/runs/discovery-gated-transformer/jet_certificate.json",
        "pointer": "$.owner_ref",
    }
    validate_dgt_hardgate_evidence_bundle(payload, root=tmp_path)


def test_dgt_passing_hardgate_evidence_pointers_must_resolve(tmp_path):
    _write_required_dgt_external_artifacts(tmp_path)
    payload = dgt.build_payload(generated_at="fixture-time")
    dgt.write_artifacts(payload, root=tmp_path)
    missing = (
        tmp_path
        / "reports"
        / "runs"
        / "discovery-gated-transformer"
        / "jet_certificate.json"
    )
    missing.unlink()

    with pytest.raises(ValueError, match="DGT hardgate evidence pointer does not resolve: DGT-HG18"):
        validate_dgt_hardgate_evidence_bundle(payload, root=tmp_path)


def test_dgt_canonical_payload_does_not_inline_sidecars():
    payload = dgt.build_payload(generated_at="fixture-time")
    sidecars = dgt.build_run_sidecars(generated_at="fixture-time")
    serialized = json.dumps(payload, sort_keys=True)

    for sidecar in sidecars.values():
        assert json.dumps(sidecar, sort_keys=True) not in serialized


def test_dgt_jet_certificate_has_required_surfaces_and_slots():
    cert = build_dgt_jet_certificate(default_dgt_source_refs())

    assert cert["schema_id"] == JET_CERTIFICATE_SCHEMA_ID
    assert cert["hardgate"]["status"] == "pass"
    assert cert["hardgate"]["gate_names"] == list(JET_HARDGATE_NAMES)
    assert {row["surface_id"] for row in cert["surface_rows"]} == set(JET_REQUIRED_SURFACES)
    for row in cert["surface_rows"]:
        for slot in JET_SURFACE_SLOTS:
            assert row[slot].startswith("reports/runs/discovery-gated-transformer/source_refs.json:$")


@pytest.mark.parametrize(
    "gate_name,mutate",
    [
        ("JET-HG1", lambda cert: cert["surface_rows"][0].pop("boundary_spec_ref")),
        ("JET-HG2", lambda cert: cert["surface_rows"][0].pop("low_order_baseline_ref")),
        ("JET-HG3", lambda cert: cert["surface_rows"][0].update({"irreducible_residual_gain": 0.0})),
        ("JET-HG4", lambda cert: cert["surface_rows"][0].pop("causal_patch_evidence_ref")),
        ("JET-HG5", lambda cert: cert["surface_rows"][0].update({"matched_random_gain": 0.1})),
        ("JET-HG6", lambda cert: cert["jet_coverage"].update({"dgt": cert["jet_coverage"]["base_control"]})),
        ("JET-HG7", lambda cert: cert["derivative_debt_ledger"]["rows"].pop()),
        ("JET-HG8", lambda cert: cert["claim_status"].update({"status": "terminal_verdict"})),
    ],
)
def test_dgt_jet_hardgates_fail_closed(gate_name, mutate):
    cert = build_dgt_jet_certificate(default_dgt_source_refs())
    mutated = json.loads(json.dumps(cert))
    mutate(mutated)
    if gate_name == "JET-HG8":
        mutated["forbidden_claim_term_audit"] = {
            "status": "fail",
            "hits": ["terminal verdict token"],
            "forbidden_terms": mutated["forbidden_claim_term_audit"]["forbidden_terms"],
        }
    hardgate = evaluate_dgt_jet_hardgates(mutated)

    assert hardgate["gates"][gate_name]["status"] == "fail"
    with pytest.raises(ValueError, match="hardgate|forbidden"):
        validate_dgt_jet_certificate({**mutated, "hardgate": hardgate, "failed_gate": hardgate["failed_gate"]})


def test_tool_route_schema_required_keys_and_pointers_resolve(tmp_path):
    _write_required_dgt_external_artifacts(tmp_path)
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


def test_dgt_tool_hg4_fails_when_blocked_route_row_removed():
    payload = dgt.build_payload(generated_at="fixture-time")
    tool_route = json.loads(json.dumps(payload["tool_route_evidence"]))
    tool_route["blocked_route_evidence"]["rows"].pop()

    hardgate = evaluate_dgt_tool_route_hardgates(tool_route)
    assert hardgate["gates"]["DGT-TOOL-HG4"]["status"] == "fail"
    with pytest.raises(ValueError, match="hardgate"):
        validate_dgt_tool_route_evidence(tool_route)


def test_dgt_tool_hg5_fails_when_not_claimed_empty():
    payload = dgt.build_payload(generated_at="fixture-time")
    tool_route = json.loads(json.dumps(payload["tool_route_evidence"]))
    tool_route["not_claimed"] = []

    hardgate = evaluate_dgt_tool_route_hardgates(tool_route)
    assert hardgate["gates"]["DGT-TOOL-HG5"]["status"] == "fail"
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


def test_dgt_family_definition_requires_architecture_objective_and_certificate_groups():
    payload = dgt.build_payload(generated_at="fixture-time")
    family_definition = payload["family_definition"]

    assert FAMILY_DEFINITION_POINTER == f"{CANONICAL_JSON_ARTIFACT}:$.family_definition"
    assert tuple(family_definition) == FAMILY_DEFINITION_REQUIRED_KEYS
    assert family_definition["owner_ref"] == f"{CANONICAL_JSON_ARTIFACT}:$"
    assert set(family_definition["invariant_groups"]) == {"architecture", "objective", "certificate"}
    assert family_definition["hardgate"]["status"] == "pass"
    assert family_definition["model_family_claim_status"] == {
        "status": "definition-recorded",
        "claim_scope": "structural pointer definition only",
        "claim_allowed": False,
    }
    for group in family_definition["invariant_groups"].values():
        assert group["required"] is True
        assert group["evidence_pointers"]
        assert all(pointer.startswith(f"{CANONICAL_JSON_ARTIFACT}:$") for pointer in group["evidence_pointers"])


def test_dgt_family_definition_blocks_model_family_claim_when_any_group_missing():
    payload = dgt.build_payload(generated_at="fixture-time")
    family_definition = json.loads(json.dumps(payload["family_definition"]))
    family_definition["invariant_groups"]["certificate"]["evidence_pointers"] = []

    hardgate = evaluate_dgt_family_definition_hardgate(family_definition)

    assert hardgate["status"] == "fail"
    assert hardgate["gates"]["DGT-FAMILY-HG3"]["status"] == "fail"
    with pytest.raises(ValueError, match="hardgate"):
        validate_dgt_family_definition({**family_definition, "hardgate": hardgate})


def test_dgt_family_definition_evidence_pointers_resolve(tmp_path):
    _write_required_dgt_external_artifacts(tmp_path)
    payload = dgt.build_payload(generated_at="fixture-time")
    dgt.write_artifacts(payload, root=tmp_path)
    family_definition = payload["family_definition"]

    assert resolve_artifact_pointer(tmp_path, FAMILY_DEFINITION_POINTER) is not None
    assert resolve_artifact_pointer(tmp_path, f"{CANONICAL_JSON_ARTIFACT}:$.family_definition.hardgate") is not None
    for group in family_definition["invariant_groups"].values():
        for pointer in group["evidence_pointers"]:
            assert resolve_artifact_pointer(tmp_path, pointer) is not None


def test_dgt_family_definition_rejects_forbidden_positive_model_family_wording():
    payload = dgt.build_payload(generated_at="fixture-time")
    family_definition = json.loads(json.dumps(payload["family_definition"]))
    family_definition["model_family_claim_status"]["status"] = "global superiority"
    family_definition["forbidden_claim_term_audit"] = {
        "status": "fail",
        "hits": ["global superiority"],
        "forbidden_terms": family_definition["forbidden_claim_term_audit"]["forbidden_terms"],
    }
    hardgate = evaluate_dgt_family_definition_hardgate(family_definition)

    assert hardgate["gates"]["DGT-FAMILY-HG4"]["status"] == "fail"
    with pytest.raises(ValueError, match="hardgate"):
        validate_dgt_family_definition({**family_definition, "hardgate": hardgate})
