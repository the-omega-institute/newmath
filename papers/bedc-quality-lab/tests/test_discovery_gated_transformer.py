import json
from copy import deepcopy

import pytest

from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer
from bedc_quality_lab.discovery_gated_transformer import (
    ARTIFACT_ID,
    CANONICAL_JSON_ARTIFACT,
    DGT_L0_CONTROLS_ARTIFACT,
    L0_FORBIDDEN_LADDER_KEYS,
    L0_HARDGATE_SUMMARY_REF,
    L0_LADDER_CONSUMPTION_REF,
    L0_REVIEW_STATUS_REF,
    L0_TOY_PROJECTION_REF,
    TOOL_ROUTE_CGA_ROUTE_PATCH_REF,
    TOOL_ROUTE_REQUIRED_KEYS,
    TOOL_ROUTE_SCHEMA_ID,
    COMPONENT_ABLATION_GATE_NAMES,
    COMPONENT_ABLATION_OWNER_REF,
    D4_PROJECTION_GATE_NAMES,
    D5M_GATE_NAMES,
    D5M_DEFAULT_EVIDENCE_SCOPE,
    D5O_GATE_NAMES,
    D5O_REVIEW_PHRASE,
    SCALING_LADDER_GATE_NAMES,
    SCALING_LADDER_LEVEL_IDS,
    LAT_CANONICAL_ARTIFACT,
    FAMILY_DEFINITION_POINTER,
    FAMILY_DEFINITION_REQUIRED_KEYS,
    GATE_NAMES,
    JET_CERTIFICATE_SCHEMA_ID,
    JET_HARDGATE_NAMES,
    JET_REQUIRED_SURFACES,
    JET_SURFACE_SLOTS,
    MODEL_ID,
    MODEL_COMPARISON_CANONICAL_ARTIFACT,
    ROBUSTNESS_GATE_NAMES,
    ROBUSTNESS_OWNER_REF,
    SCHEMA_ID,
    build_dgt_jet_certificate,
    build_d4_projection_payload,
    build_component_ablation,
    build_projection,
    build_d5_m_projection,
    build_d5_o_projection,
    build_scaling_ladder_projection,
    d5_m_hardgate_rows,
    scaling_ladder_hardgate_rows,
    _owner_refs_resolve,
    _toy_seed_surface_summary,
    default_robustness_source_payloads,
    evaluate_ablation_arm,
    evaluate_operational_robustness_hardgates,
    evaluate_dgt_family_definition_hardgate,
    evaluate_dgt_jet_hardgates,
    evaluate_dgt_tool_route_hardgates,
    arm_catalog,
    default_component_refs,
    default_dgt_source_refs,
    metric_contract,
    validate_component_ablation,
    validate_projection,
    validate_dgt_hardgate_evidence_bundle,
    validate_dgt_family_definition,
    validate_dgt_jet_certificate,
    validate_dgt_tool_route_evidence,
    validate_d4_projection,
    validate_d5_m_projection,
    validate_d5_m_scope,
    validate_d5_o_projection,
    validate_scaling_ladder_projection,
    validate_operational_robustness,
)
from bedc_quality_lab import dgt_l0_controls
from bedc_quality_lab import dgt_l1_controls
from bedc_quality_lab import dgt_base_undertraining_audit
from bedc_quality_lab import fair_l1_decision
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
    canonical_dir = root / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    (canonical_dir / "new_model_hardgates.json").write_text(json.dumps({"gates": {"status": "pass"}}) + "\n", encoding="utf-8")
    (canonical_dir / "mechanism_dna.json").write_text(json.dumps({"rows": [{"status": "pass"}]}) + "\n", encoding="utf-8")
    (canonical_dir / "discovery_map.json").write_text(json.dumps({"coverage_matrix": {"status": "pointer-only"}}) + "\n", encoding="utf-8")
    (canonical_dir / "discovery-gated-transformer-training.json").write_text(json.dumps({"hardgates": {"status": "pass"}}) + "\n", encoding="utf-8")
    (canonical_dir / "dgt-neural-ablation.json").write_text(json.dumps({"nabl_hardgates": {"status": "pass"}}) + "\n", encoding="utf-8")


def _write_passed_dgt_neural_ablation_artifact(root):
    canonical_dir = root / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    claims = [
        {
            "claim_scope": "bounded toy training",
            "claim_status": "allowed",
            "component": "LAT",
            "evidence_scope": ["small-real-training"],
        }
    ]
    (canonical_dir / "dgt-neural-ablation.json").write_text(
        json.dumps({"component_causal_claims": claims, "nabl_hardgates": {"status": "pass"}}) + "\n",
        encoding="utf-8",
    )


def _write_passed_dgt_l0_controls_artifact(root):
    payload = dgt_l0_controls.build_payload(generated_at="fixture-time", requested_device="cpu")
    dgt_l0_controls.write_artifacts(payload, root=root, generated_at="fixture-time")
    return payload


def _write_ready_dgt_l1_controls_artifact(root):
    input_path = root / fair_l1_decision.INPUT_ACCESSIBILITY_ARTIFACT
    input_path.parent.mkdir(parents=True, exist_ok=True)
    input_path.write_bytes((fair_l1_decision.LAB_ROOT / fair_l1_decision.INPUT_ACCESSIBILITY_ARTIFACT).read_bytes())
    payload = dgt_l1_controls.build_payload(generated_at="fixture-time", requested_device="cpu")
    dgt_l1_controls.write_artifacts(payload, root=root, generated_at="fixture-time")
    base_payload = dgt_base_undertraining_audit.build_payload(root=root, generated_at="fixture-time")
    dgt_base_undertraining_audit.write_artifacts(base_payload, root=root, generated_at="fixture-time")
    fair_payload = fair_l1_decision.build_payload(root=root, generated_at="fixture-time")
    fair_l1_decision.write_artifacts(fair_payload, root=root, generated_at="fixture-time")
    return payload


def _write_eligible_fair_l1_decision_artifact(root):
    path = root / fair_l1_decision.CANONICAL_JSON_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "decision": {"status": "scaling-evidence-eligible"},
                "ladder_state_projection": {
                    "state": "l1-scaling-evidence-eligible",
                    "decision_status": "scaling-evidence-eligible",
                    "decision_pointer": "reports/canonical/fair-l1-decision.json:$.decision.status",
                    "hardgate_pointer": "reports/canonical/fair-l1-decision.json:$.hardgates",
                    "boundary_ledger_pointer": "reports/canonical/fair-l1-decision.json:$.boundary_ledger",
                    "not_claimed": [
                        "Bounded tiny-sequence L1 decision only.",
                        "No L2 or higher scaling claim.",
                        "No production deployment claim.",
                        "No global superiority claim.",
                        "No LLM replacement claim.",
                        "No OOD generalization claim.",
                        "No architecture advantage claim.",
                    ],
                },
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def _write_dgt_owner_refs(root):
    _write_passed_dgt_l0_controls_artifact(root)
    _write_ready_dgt_l1_controls_artifact(root)


def _accepted_dgt_review_rows():
    return [
        {
            "claim_id": "claim:discovery-gated-transformer",
            "status": "pass",
            "reason": "positive-discovery-gates-pass",
            "ledger_pointer": "reports/canonical/high-impact-review.json:$.review_rows[0]",
            "claim_pointer": "reports/canonical/discovery-gated-transformer.json:$.d4_projection",
        }
    ]


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
    assert payload["operational_robustness"]["owner_ref"] == ROBUSTNESS_OWNER_REF
    assert payload["operational_robustness"]["readiness"] == "ready"
    assert payload["operational_robustness"]["discovery_level"] == "D5-O"
    assert tuple(payload["operational_robustness"]["hardgate"]["gates"]) == ROBUSTNESS_GATE_NAMES
    assert payload["operational_robustness"]["source_artifacts"]["ledger_aware_transformer_pointer"] == f"{LAT_CANONICAL_ARTIFACT}:$"
    assert payload["source_artifacts"]["model_comparison_pointer"] == f"{MODEL_COMPARISON_CANONICAL_ARTIFACT}:$"


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


def test_dgt_component_ablation_has_exact_eleven_owner_local_arms():
    payload = dgt.build_payload(generated_at="fixture-time")
    ablation = payload["component_ablation"]

    assert ablation["owner_ref"] == COMPONENT_ABLATION_OWNER_REF
    assert ablation["arm_count"] == 11
    assert [row["arm_id"] for row in ablation["arms"]] == [spec.arm_id for spec in arm_catalog()]
    assert ablation["metric_contract"] == metric_contract()
    assert ablation["hardgate"]["gate_names"] == list(COMPONENT_ABLATION_GATE_NAMES)
    assert ablation["hardgate"]["status"] == "pass"
    assert ablation["failed_gate"] == []
    for row in ablation["arms"]:
        assert row["component_pointer"].startswith(f"{CANONICAL_JSON_ARTIFACT}:$")
        assert row["metric_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.component_ablation.metric_contract"
        assert row["claim_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.component_ablation.claim_policy"


def test_dgt_component_ablation_measurable_arms_allow_causal_claims():
    spec = arm_catalog()[0]
    row = evaluate_ablation_arm(spec, 1105)

    assert row["measured_effect"] >= metric_contract()["measurable_effect_threshold"]
    assert row["effect_status"] == "measurable"
    assert row["causal_claim_allowed"] is True

    ablation = build_component_ablation()
    mutated = json.loads(json.dumps(ablation))
    mutated["arms"][0]["effect_status"] = "zero-effect-fail-closed"
    mutated["arms"][0]["causal_claim_allowed"] = False

    with pytest.raises(ValueError, match="hardgate"):
        validate_component_ablation(mutated)


def test_dgt_component_ablation_zero_effect_fails_closed():
    spec = arm_catalog()[0]
    zero_spec = type(spec)(
        arm_id=spec.arm_id,
        component=spec.component,
        disabled_components=spec.disabled_components,
        expected_signal_delta=0.0,
    )
    row = evaluate_ablation_arm(zero_spec, 1105)

    assert row["effect_status"] == "zero-effect-fail-closed"
    assert row["causal_claim_allowed"] is False

    ablation = build_component_ablation()
    mutated = json.loads(json.dumps(ablation))
    mutated["arms"][0]["measured_effect"] = 0.0
    mutated["arms"][0]["effect_status"] = "zero-effect-fail-closed"
    mutated["arms"][0]["causal_claim_allowed"] = True

    with pytest.raises(ValueError, match="hardgate"):
        validate_component_ablation(mutated)


def test_dgt_component_ablation_rejects_missing_arm_and_standalone_claims():
    ablation = build_component_ablation()
    missing = json.loads(json.dumps(ablation))
    missing["arms"].pop()
    missing["arm_count"] = 10

    with pytest.raises(ValueError, match="arm count|arm catalog|hardgate"):
        validate_component_ablation(missing)

    forbidden = json.loads(json.dumps(ablation))
    forbidden["claim_policy"]["owner_scope"] = "production global superiority formal closure"
    forbidden["forbidden_claim_term_audit"] = {
        "status": "fail",
        "hits": ["production", "global superiority", "formal closure"],
        "forbidden_terms": forbidden["forbidden_claim_term_audit"]["forbidden_terms"],
    }

    with pytest.raises(ValueError, match="hardgate"):
        validate_component_ablation(forbidden)


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


@pytest.mark.parametrize(
    ("gate_name", "mutate"),
    [
        ("PROJ-HG1", lambda payload: payload["hardgate"].update({"status": "fail"})),
        ("PROJ-HG2", lambda payload: payload["tool_route_evidence"]["hardgate"].update({"status": "fail"})),
        ("PROJ-HG3", lambda payload: payload["tool_route_evidence"].update({"net_positive_signal": False})),
        (
            "PROJ-HG4",
            lambda payload: payload["tool_route_evidence"]["classifier_surface_delta"]["route_math_lookup_positive"].update(
                {"surface_delta_count": 0}
            ),
        ),
        ("PROJ-HG5", lambda payload: payload["family_definition"]["hardgate"].update({"status": "fail"})),
        ("PROJ-HG6", lambda payload: payload["claim_capsule_ref"].update({"pointer": ""})),
        ("PROJ-HG7", lambda payload: payload.update({"not_claimed": []})),
        ("PROJ-HG8", lambda payload: payload["forbidden_claim_term_audit"].update({"status": "fail"})),
        ("PROJ-HG9", lambda payload: payload.update({"terminal_verdict": "accepted_positive_discovery"})),
        ("PROJ-HG10", lambda payload: payload["discovery_map_signal_ref"].update({"pointer": ""})),
    ],
)
def test_dgt_d4_projection_fails_closed_for_each_proj_gate(gate_name, mutate):
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutate(mutated)

    projection = build_d4_projection_payload(mutated, payload["d4_projection"]["core_contracts"])

    assert projection["gates"][gate_name]["status"] == "fail"
    assert projection["discovery_level"] == "D0"
    assert projection["readiness"] == "blocked"
    assert projection["failed_gate"] == gate_name
    assert projection["failed_gate_pointer"].endswith(f"$.d4_projection.gates.{gate_name}")
    assert projection["blocked_reason"] == f"blocked-by-{gate_name}"
    assert projection["anti_triviality_status"] == "fail"
    assert projection["anti_triviality_failed_gate"] == gate_name
    assert projection["claim_basis"]["positive_discovery"] is False
    assert validate_d4_projection(projection, mutated) == []


def test_dgt_d4_projection_rejects_terminal_verdict_surface():
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload["d4_projection"]))
    mutated["claim_basis"]["terminal_verdict"] = "accepted_positive_discovery"

    assert "forbidden authority token" in "; ".join(validate_d4_projection(mutated, payload))


def test_dgt_d5_o_projection_requires_terminal_d4_acceptance(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(generated_at="fixture-time", claim_verdict_rows=[], root=tmp_path)

    projection = payload["d5_o_projection"]

    assert projection["gates"]["D5O-HG1"]["status"] == "fail"
    assert projection["status"] == "blocked"
    assert projection["discovery_level"] == "D4"
    assert projection["blocked_reason"] == "blocked-by-D5O-HG1"


def test_dgt_d5_o_projection_passes_with_terminal_d4_acceptance(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )

    projection = payload["d5_o_projection"]

    assert tuple(projection["gates"]) == D5O_GATE_NAMES
    assert projection["gate_status"] == "pass"
    assert projection["status"] == "ready"
    assert projection["discovery_level"] == "D5-O"
    assert projection["source_level"] == "D4"
    assert validate_d5_o_projection(projection, payload) == []


def test_dgt_d5_o_projection_has_at_least_three_nontrivial_ood_passes(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    summary = payload["d5_o_projection"]["surface_summary"]

    assert summary["nontrivial_ood_pass_count"] >= 3
    assert summary["nontrivial_ood_pass_count"] >= summary["required_nontrivial_ood_pass_count"]
    assert all(row["owner_pass"] for row in summary["surfaces"])


def test_dgt_d5_o_projection_seed_expansion_passes(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    summary = payload["d5_o_projection"]["surface_summary"]

    assert summary["seed"] == 1105
    assert len({row["seed"] for row in summary["surfaces"]}) >= 4
    assert payload["d5_o_projection"]["gates"]["D5O-HG4"]["status"] == "pass"


def test_dgt_d5_o_projection_threshold_frontier_passes(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    frontier = payload["d5_o_projection"]["surface_summary"]["threshold_frontier"]

    assert frontier["frontier_status"] == "pass"
    assert frontier["owner_pass_count"] >= 3
    assert payload["d5_o_projection"]["gates"]["D5O-HG5"]["status"] == "pass"


def test_dgt_d5_o_projection_stronger_matched_random_remains_negative(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    frontier = payload["d5_o_projection"]["surface_summary"]["threshold_frontier"]

    assert frontier["matched_random_pass_count"] == 0
    assert payload["d5_o_projection"]["gates"]["D5O-HG6"]["status"] == "pass"


def test_dgt_d5_o_projection_failed_surfaces_boundary_ledgers(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(generated_at="fixture-time", claim_verdict_rows=[], root=tmp_path)
    projection = payload["d5_o_projection"]

    assert projection["gates"]["D5O-HG1"]["status"] == "fail"
    assert any(row["gate"] == "D5O-HG1" and row["status"] == "fail" for row in projection["boundary_ledger"])
    assert projection["blocked_reason"] == "blocked-by-D5O-HG1"
    assert projection["evidence_pointers"]["terminal_d4_acceptance"].endswith("$.review_rows[0]")


def _assert_d5_o_fail_closed(projection, gate_name):
    assert projection["gates"][gate_name]["status"] == "fail"
    assert projection["gate_status"] == "fail"
    assert projection["status"] == "blocked"
    assert projection["discovery_level"] == "D4"
    assert projection["blocked_reason"] == f"blocked-by-{gate_name}"
    assert projection["anti_triviality_status"] == "fail"
    assert projection["anti_triviality_failed_gate"] == gate_name
    assert any(row["gate"] == gate_name and row["status"] == "fail" for row in projection["boundary_ledger"])


def test_dgt_d5_o_hg2_fails_closed_when_d4_source_not_ready(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(generated_at="fixture-time", high_impact_review_rows=_accepted_dgt_review_rows(), root=tmp_path)
    mutated = json.loads(json.dumps(owner))
    mutated["d4_projection"]["readiness"] = "blocked"
    mutated["d4_projection"]["failed_gate"] = "PROJ-HG1"
    projection = build_d5_o_projection(mutated, _accepted_dgt_review_rows(), root=tmp_path)

    _assert_d5_o_fail_closed(projection, "D5O-HG2")
    assert validate_d5_o_projection(projection, mutated) == []


def test_dgt_d5_o_hg3_fails_closed_when_ood_surface_count_is_below_three(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(generated_at="fixture-time", high_impact_review_rows=_accepted_dgt_review_rows(), root=tmp_path)
    summary = _toy_seed_surface_summary()
    summary["required_nontrivial_ood_pass_count"] = 5
    projection = build_d5_o_projection(owner, _accepted_dgt_review_rows(), root=tmp_path, surface_summary=summary)

    _assert_d5_o_fail_closed(projection, "D5O-HG3")
    assert projection["surface_summary"]["nontrivial_ood_pass_count"] < projection["surface_summary"]["required_nontrivial_ood_pass_count"]


def test_dgt_d5_o_hg4_fails_closed_when_seed_expansion_is_missing(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(generated_at="fixture-time", high_impact_review_rows=_accepted_dgt_review_rows(), root=tmp_path)
    summary = _toy_seed_surface_summary()
    for row in summary["surfaces"]:
        row["seed"] = 1105
    projection = build_d5_o_projection(owner, _accepted_dgt_review_rows(), root=tmp_path, surface_summary=summary)

    _assert_d5_o_fail_closed(projection, "D5O-HG4")
    assert len({row["seed"] for row in projection["surface_summary"]["surfaces"]}) == 1


def test_dgt_d5_o_hg5_fails_closed_when_threshold_frontier_is_missing(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(generated_at="fixture-time", high_impact_review_rows=_accepted_dgt_review_rows(), root=tmp_path)
    summary = _toy_seed_surface_summary()
    summary.pop("threshold_frontier")
    projection = build_d5_o_projection(owner, _accepted_dgt_review_rows(), root=tmp_path, surface_summary=summary)

    _assert_d5_o_fail_closed(projection, "D5O-HG5")
    assert projection["gates"]["D5O-HG5"]["evidence"]["pointer"].endswith("threshold_frontier")


def test_dgt_d5_o_hg6_fails_closed_when_matched_random_is_not_negative(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(generated_at="fixture-time", high_impact_review_rows=_accepted_dgt_review_rows(), root=tmp_path)
    summary = _toy_seed_surface_summary()
    summary["surfaces"][0]["matched_random_pass"] = True
    projection = build_d5_o_projection(owner, _accepted_dgt_review_rows(), root=tmp_path, surface_summary=summary)

    _assert_d5_o_fail_closed(projection, "D5O-HG6")
    assert any(row["matched_random_pass"] is True for row in projection["surface_summary"]["surfaces"])


def test_dgt_d5_o_hg7_fails_closed_when_operational_dependency_is_missing(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(generated_at="fixture-time", high_impact_review_rows=_accepted_dgt_review_rows(), root=tmp_path)
    mutated = json.loads(json.dumps(owner))
    mutated["operational_robustness"]["hardgate"]["status"] = "fail"
    projection = build_d5_o_projection(mutated, _accepted_dgt_review_rows(), root=tmp_path)

    _assert_d5_o_fail_closed(projection, "D5O-HG7")
    assert projection["gates"]["D5O-HG7"]["evidence"]["pointer"].endswith("boundary_ledger")


def test_dgt_d5_o_hg8_fails_closed_when_boundary_text_is_missing(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(generated_at="fixture-time", high_impact_review_rows=_accepted_dgt_review_rows(), root=tmp_path)
    not_claimed = ["Bounded D5-O claim over deterministic toy surfaces only."]
    projection = build_d5_o_projection(owner, _accepted_dgt_review_rows(), root=tmp_path, not_claimed=not_claimed)

    _assert_d5_o_fail_closed(projection, "D5O-HG8")
    assert projection["not_claimed"] == not_claimed


def test_dgt_d5_o_projection_no_global_robustness_claim_in_positive_text(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    projection = payload["d5_o_projection"]
    positive_text = json.dumps(
        {
            "scope": projection["scope"],
            "status": projection["status"],
            "discovery_level": projection["discovery_level"],
        },
        sort_keys=True,
    ).lower()

    assert "global robustness" not in positive_text
    assert "production" not in positive_text
    assert "llm replacement" not in positive_text


def test_dgt_d5_o_projection_high_impact_review_wording_present(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )

    assert payload["d5_o_projection"]["scope"]["review"] == D5O_REVIEW_PHRASE


def test_dgt_d5_m_projection_passes_with_closed_bounded_mechanism(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    projection = payload["d5_m_projection"]

    assert tuple(projection["hardgates"]) == D5M_GATE_NAMES
    assert projection["discovery_level"] == "D5-M"
    assert projection["readiness"] == "ready"
    assert projection["failed_gate"] is None
    assert projection["evidence_scope"] == list(D5M_DEFAULT_EVIDENCE_SCOPE)
    assert projection["terminal_verdict_scope"] == "Core"
    assert projection["mechanism_certificate_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.mechanism_namecert_ref"
    assert projection["jet_certificate_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref"
    assert projection["causal_patch_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness"
    assert projection["component_ablation_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.neural_ablation_ref"
    assert validate_d5_m_projection(payload) == []


def test_dgt_d5_m_scope_marks_projection_as_bounded_synthetic(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    scope = payload["d5_m_scope"]

    assert scope["basis"] == "bounded_synthetic"
    assert scope["synthetic_bounded"] is True
    assert scope["aliases"] == ["discovery-gated-transformer"]
    assert scope["model_comparison_pointer"] == f"{MODEL_COMPARISON_CANONICAL_ARTIFACT}:$"
    assert scope["model_comparison_semantic_pointer"] == f"{MODEL_COMPARISON_CANONICAL_ARTIFACT}:$.comparisons[0].semantic"
    assert scope["allowed_claim_kinds"] == ["synthetic_boundary", "protocol_projection"]
    assert "No trained-model evidence claim from projection artifacts." in scope["not_claimed"]
    assert validate_d5_m_scope(payload) == []


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (lambda scope: scope.update({"model_comparison_semantic_pointer": "reports/canonical/model-comparison.json:$.comparisons[99].semantic"}), "semantic pointer"),
        (lambda scope: scope.update({"basis": "training_evidence_clean", "synthetic_bounded": False}), "allowed claim kinds"),
        (lambda scope: scope.update({"not_claimed": ["No production or deployment authority claim."]}), "not_claimed missing boundary"),
    ],
)
def test_dgt_d5_m_scope_mutations_fail_closed(tmp_path, mutate, message):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    mutated = deepcopy(payload)
    mutate(mutated["d5_m_scope"])

    errors = validate_d5_m_scope(mutated)

    assert any(message in error for error in errors)


def _assert_d5_m_fail_closed(owner_payload, gate_name):
    projection = owner_payload["d5_m_projection"]
    assert projection["hardgates"][gate_name]["status"] == "fail"
    assert projection["gate_status"] == "fail"
    assert projection["status"] == "blocked"
    assert projection["readiness"] == "blocked"
    assert projection["discovery_level"] == projection["source_level"]
    assert projection["blocked_reason"] == f"blocked-by-{gate_name}"
    assert projection["failed_gate"] == gate_name
    assert any(row["gate"] == gate_name and row["status"] == "fail" for row in projection["boundary_ledger"])
    assert validate_d5_m_projection(owner_payload) == []


@pytest.mark.parametrize(
    ("gate_name", "mutate"),
    [
        ("D5M-HG1", lambda payload: payload["d5_o_projection"].update({"status": "blocked"})),
        ("D5M-HG2", lambda payload: payload["d5_m_projection"].pop("evidence_scope")),
        ("D5M-HG3", lambda payload: payload["d5_m_projection"].update({"mechanism_closure_status": "open"})),
        ("D5M-HG4", lambda payload: payload["d5_m_projection"].update({"jet_certificate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.missing_jet"})),
        ("D5M-HG5", lambda payload: payload["operational_robustness"]["hardgate"].update({"status": "fail"})),
        ("D5M-HG6", lambda payload: payload["neural_ablation_ref"].update({"pointer": "$.nabl_hardgates.failed_gate"})),
        ("D5M-HG7", lambda payload: payload["d5_m_projection"]["negative_witness_pointers"].update({"score_margin_shortcut": "uncleared"})),
        ("D5M-HG8", lambda payload: payload["d5_m_projection"]["negative_witness_pointers"].update({"scale_leakage": "uncleared"})),
        ("D5M-HG9", lambda payload: payload["d4_projection"]["matched_control"].update({"control_positive": True})),
        ("D5M-HG10", lambda payload: payload["d5_m_projection"].update({"terminal_verdict_scope": "Global"})),
    ],
)
def test_dgt_d5_m_projection_fails_closed_on_each_hardgate(tmp_path, gate_name, mutate):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    mutated = json.loads(json.dumps(owner))
    mutate(mutated)
    mutated["d5_m_projection"] = build_d5_m_projection(mutated)

    _assert_d5_m_fail_closed(mutated, gate_name)
    if gate_name != "D5M-HG2":
        assert d5_m_hardgate_rows(mutated)[gate_name]["status"] == "fail"


def test_dgt_d5_m_projection_rejects_forbidden_claim_surface(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    mutated = json.loads(json.dumps(owner))
    mutated["d5_m_projection"]["not_claimed"] = ["Bounded D5-M mechanism claim only."]
    mutated["d5_m_projection"] = build_d5_m_projection(mutated)

    _assert_d5_m_fail_closed(mutated, "D5M-HG10")


@pytest.mark.parametrize(
    "evidence_scope",
    [
        "bounded-design",
        [],
        ["bounded-design", "bounded-design"],
        ["bounded-design", "unbounded-model"],
    ],
)
def test_dgt_d5_m_projection_rejects_invalid_evidence_scope(tmp_path, evidence_scope):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    mutated = json.loads(json.dumps(owner))
    mutated["d5_m_projection"]["evidence_scope"] = evidence_scope

    with pytest.raises(ValueError, match="evidence_scope"):
        build_d5_m_projection(mutated)


def test_dgt_d5_m_missing_evidence_scope_blocks_positive_claim(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    mutated = json.loads(json.dumps(owner))
    mutated["d5_m_projection"].pop("evidence_scope")
    projection = build_d5_m_projection(mutated)

    assert projection["status"] == "blocked"
    assert projection["readiness"] == "blocked"
    assert projection["discovery_level"] == "D5-O"
    assert projection["failed_gate"] == "D5M-HG2"
    assert projection["blocked_reason"] == "blocked-by-D5M-HG2"
    assert projection["evidence_scope"] == list(D5M_DEFAULT_EVIDENCE_SCOPE)
    assert any(row["gate"] == "D5M-HG2" and row["status"] == "fail" for row in projection["boundary_ledger"])


def test_dgt_d5_m_production_forbidden_rejects_production_claim(tmp_path):
    _write_dgt_owner_refs(tmp_path)
    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    mutated = json.loads(json.dumps(owner))
    mutated["d5_m_projection"]["terminal_verdict_scope"] = "production deployment authority"

    with pytest.raises(ValueError, match="production claim|forbidden_claim_audit|D5M-HG10"):
        build_d5_m_projection(mutated)


def _ready_scaling_level(level_id, index):
    if level_id == "L0_toy":
        return {
            "level_id": level_id,
            "claim_id": f"claim:dgt_scaling_ladder_owner:{level_id}",
            "l0_toy_projection_ref": dict(L0_TOY_PROJECTION_REF),
            "review_status_ref": dict(L0_REVIEW_STATUS_REF),
            "hardgate_summary_ref": dict(L0_HARDGATE_SUMMARY_REF),
            "ladder_consumption_ref": dict(L0_LADDER_CONSUMPTION_REF),
            "review_status_alias": "pass",
            "ladder_consumption_status": "open",
            "review_status_alias_source": f"{DGT_L0_CONTROLS_ARTIFACT}:$.l0_toy_projection.review_status",
            "projected_claim_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.scaling_ladder.levels[{index}].claim_capsule",
            "level_state": "open",
            "promotion_status": "opened-from-l0-pass-pointer",
            "boundary_ledger": [],
            "not_claimed": [
                "Bounded L0 toy training controls only.",
                "No production scale claim.",
                "No GPT or Llama claim.",
                "No global superiority claim.",
                "No LLM replacement claim.",
                "No universal recipe claim.",
                "No unbounded scaling law claim.",
                "No verdict inheritance to L1 or higher scaling levels.",
            ],
        }
    return {
        "level_id": level_id,
        "claim_id": f"claim:dgt_scaling_ladder_owner:{level_id}",
        "raw_claim_pointer": f"reports/runs/discovery-gated-transformer/scaling/{level_id}/claim_capsule.json:$",
        "projected_claim_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.scaling_ladder.levels[{index}].claim_capsule",
        "level_state": "ready",
        "promotion_status": "level-local-evidence-ready",
        "base_transformer_control": {
            "status": "pass",
            "pointer": f"reports/runs/discovery-gated-transformer/scaling/{level_id}/base_transformer_control.json:$",
        },
        "matched_random_structural_control": {
            "status": "pass",
            "pointer": f"reports/runs/discovery-gated-transformer/scaling/{level_id}/matched_random_structural_control.json:$",
        },
        "compute_param_ledger": {
            "status": "pass",
            "compute_units": (index + 1) * 100,
            "parameter_count": (index + 1) * 10,
            "pointer": f"reports/runs/discovery-gated-transformer/scaling/{level_id}/compute_param_ledger.json:$",
        },
        "negative_witness_sweep": {
            "status": "pass",
            "pointer": f"reports/runs/discovery-gated-transformer/scaling/{level_id}/negative_witness_sweep.json:$",
        },
        "hardgates": {"SCALE-HG2": "pass", "SCALE-HG3": "pass", "SCALE-HG4": "pass"},
        "boundary_ledger": [],
        "not_claimed": [
            "Bounded model prototype scaling only.",
            "No production scale claim.",
            "No GPT or Llama claim.",
            "No global superiority claim.",
            "No LLM replacement claim.",
            "No universal recipe claim.",
            "No unbounded scaling law claim.",
        ],
    }


def _owner_with_ready_scaling_ladder(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    _write_eligible_fair_l1_decision_artifact(tmp_path)
    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    l1_capsule = owner["scaling_ladder"]["levels"][1]["claim_capsule"]
    owner["scaling_ladder"] = {
        "levels": [
            {"level_id": level_id, "claim_capsule": l1_capsule if level_id == "L1_tiny_sequence" else _ready_scaling_level(level_id, index)}
            for index, level_id in enumerate(SCALING_LADDER_LEVEL_IDS)
        ]
    }
    owner["scaling_ladder"] = build_scaling_ladder_projection(owner)
    return owner


def _owner_with_l1_open_scaling_ladder(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    return dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )


def test_dgt_scaling_ladder_defaults_to_d5_m_boundary_without_claiming_scaling(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    ladder = payload["scaling_ladder"]

    assert tuple(ladder["hardgate"]["gates"]) == SCALING_LADDER_GATE_NAMES
    assert [row["level_id"] for row in ladder["levels"]] == list(SCALING_LADDER_LEVEL_IDS)
    assert ladder["status"] == "blocked"
    assert ladder["review_status"] == "review-line-blocked"
    assert ladder["discovery_level"] == "D5-M"
    assert ladder["hardgate"]["failed_gate"] in {"SCALE-HG2", "SCALE-HG5"}
    assert ladder["evidence_scope"] == "bounded-model-prototype-scaling"
    assert validate_scaling_ladder_projection(payload) == []


def test_dgt_scaling_ladder_claim_capsule_self_pointers_resolve(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )

    for level_index, row in enumerate(payload["scaling_ladder"]["levels"]):
        capsule = row["claim_capsule"]
        for key, value in capsule.items():
            if not key.endswith("_pointer"):
                continue
            artifact, local_pointer = value.split(":", 1)
            if artifact != CANONICAL_JSON_ARTIFACT:
                continue
            resolved = pointer_value(payload, local_pointer)
            assert resolved is not None, (level_index, row["level_id"], key, value)


def test_dgt_scaling_ladder_l0_projects_from_canonical_controls_without_inheriting_l1(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    ladder = owner["scaling_ladder"]
    l0_capsule = ladder["levels"][0]["claim_capsule"]

    assert l0_capsule["level_state"] == "scoped-boundary"
    assert l0_capsule["promotion_status"] == "scoped-boundary-from-l0-owner-pointer"
    assert l0_capsule["l0_toy_projection_ref"] == L0_TOY_PROJECTION_REF
    assert l0_capsule["review_status_ref"] == L0_REVIEW_STATUS_REF
    assert l0_capsule["hardgate_summary_ref"] == L0_HARDGATE_SUMMARY_REF
    assert l0_capsule["ladder_consumption_ref"] == L0_LADDER_CONSUMPTION_REF
    assert l0_capsule["review_status_alias"] == "scoped-boundary"
    assert l0_capsule["ladder_consumption_status"] == "scoped-boundary"
    assert l0_capsule["review_status_alias_source"] == f"{DGT_L0_CONTROLS_ARTIFACT}:$.l0_toy_projection.review_status"
    assert not any(key in l0_capsule for key in L0_FORBIDDEN_LADDER_KEYS)
    assert ladder["opened_levels"] == []
    assert ladder["overall_status"] == "blocked"
    assert ladder["not_inherited_from_l0"] == list(SCALING_LADDER_LEVEL_IDS[1:])
    assert ladder["status"] == "blocked"
    assert ladder["boundary_ledger"][0]["level_id"] == "L0_toy"
    assert validate_scaling_ladder_projection(owner) == []


def test_dgt_scaling_ladder_does_not_recompute_l0_hardgates_or_read_downstream_verdicts(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    (tmp_path / "reports" / "canonical" / "claim_verdicts.jsonl").write_text(
        json.dumps({"claim_id": "claim:dgt_scaling_ladder_owner:L0_toy", "status": "blocked"}) + "\n",
        encoding="utf-8",
    )
    (tmp_path / "reports" / "canonical" / "discovery_map.json").write_text(
        json.dumps({"coverage_matrix": {"status": "blocked"}, "terminal_verdict": "blocked"}) + "\n",
        encoding="utf-8",
    )

    payload = dgt.build_payload(
        generated_at="fixture-time",
        claim_verdict_rows=[{"claim_id": "claim:dgt_scaling_ladder_owner:L0_toy", "status": "blocked"}],
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    ladder = payload["scaling_ladder"]
    l0_capsule = ladder["levels"][0]["claim_capsule"]

    assert l0_capsule["level_state"] == "scoped-boundary"
    assert l0_capsule["ladder_consumption_status"] == "scoped-boundary"
    assert ladder["opened_levels"] == []
    assert not any(key in l0_capsule for key in L0_FORBIDDEN_LADDER_KEYS)
    serialized = json.dumps(ladder, sort_keys=True)
    assert "L0-PASS-HG" not in serialized
    assert "terminal_verdict" not in serialized
    assert "claim_verdicts" not in serialized
    assert "discovery_map" not in serialized


def test_dgt_scaling_ladder_projects_only_when_all_levels_pass(tmp_path):
    owner = _owner_with_ready_scaling_ladder(tmp_path)
    ladder = owner["scaling_ladder"]

    assert ladder["status"] == "ready"
    assert ladder["review_status"] == "review-line-ready"
    assert ladder["discovery_level"] == "D5-M"
    assert ladder["hardgate"]["status"] == "pass"
    assert ladder["hardgate"]["failed_gate"] is None
    assert ladder["boundary_ledger"] == []
    assert validate_scaling_ladder_projection(owner) == []


@pytest.mark.parametrize(
    ("gate_name", "mutate"),
    [
        ("SCALE-HG1", lambda payload: payload["d5_m_projection"].update({"status": "blocked"})),
        ("SCALE-HG2", lambda payload: payload["scaling_ladder"]["levels"][0]["claim_capsule"].update({"level_state": "blocked"})),
        ("SCALE-HG3", lambda payload: payload["scaling_ladder"]["levels"][2]["claim_capsule"]["compute_param_ledger"].update({"compute_units": 0})),
        ("SCALE-HG4", lambda payload: payload["scaling_ladder"]["levels"][2]["claim_capsule"]["negative_witness_sweep"].update({"status": "fail"})),
        ("SCALE-HG6", lambda payload: payload["scaling_ladder"].update({"evidence_scope": "production-scale"})),
    ],
)
def test_dgt_scaling_ladder_fails_closed_on_each_hardgate(tmp_path, gate_name, mutate):
    owner = _owner_with_ready_scaling_ladder(tmp_path)
    mutated = json.loads(json.dumps(owner))
    mutate(mutated)
    mutated["scaling_ladder"] = build_scaling_ladder_projection(mutated)
    ladder = mutated["scaling_ladder"]

    assert ladder["hardgate"]["gates"][gate_name]["status"] == "fail"
    assert ladder["status"] == "blocked"
    assert ladder["hardgate"]["failed_gate"] == gate_name
    assert ladder["hardgate"]["blocked_reason"] == f"blocked-by-{gate_name}"
    assert scaling_ladder_hardgate_rows(mutated)[gate_name]["status"] == "fail"
    assert validate_scaling_ladder_projection(mutated) == []


def test_dgt_scaling_ladder_hg5_fails_closed_on_unclosed_boundary_ledger(tmp_path):
    owner = _owner_with_ready_scaling_ladder(tmp_path)
    mutated = json.loads(json.dumps(owner))
    mutated["scaling_ladder"]["boundary_ledger"] = [
        {
            "level_id": "L3_byte_lm",
            "status": "failed",
            "failed_gate": "SCALE-HG5",
            "reason": "fixture stale inherited verdict",
            "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.scaling_ladder.levels[3].claim_capsule",
        }
    ]

    rows = scaling_ladder_hardgate_rows(mutated)

    assert rows["SCALE-HG5"]["status"] == "fail"
    assert rows["SCALE-HG2"]["status"] == "pass"


def test_dgt_scaling_ladder_capsules_are_level_independent(tmp_path):
    owner = _owner_with_ready_scaling_ladder(tmp_path)
    capsules = [row["claim_capsule"] for row in owner["scaling_ladder"]["levels"]]
    claim_sources = [
        capsule["l0_toy_projection_ref"]["pointer"]
        if capsule["level_id"] == "L0_toy"
        else capsule["pointer"]
        if capsule["level_id"] == "L1_tiny_sequence"
        else capsule["raw_claim_pointer"]
        for capsule in capsules
    ]

    assert len({capsule["claim_id"] for capsule in capsules}) == len(SCALING_LADDER_LEVEL_IDS)
    assert len(set(claim_sources)) == len(SCALING_LADDER_LEVEL_IDS)
    assert all(capsule["level_id"] in capsule["claim_id"] for capsule in capsules)


def test_dgt_scaling_ladder_l1_pointer_only(tmp_path):
    owner = _owner_with_l1_open_scaling_ladder(tmp_path)
    l1_capsule = owner["scaling_ladder"]["levels"][1]["claim_capsule"]

    assert l1_capsule["pointer"] == "reports/canonical/fair-l1-decision.json:$.ladder_state_projection"
    assert l1_capsule["review_status_alias"] == "bounded-negative"
    assert l1_capsule["promotion_readiness_alias"] == "l1-bounded-negative"
    assert l1_capsule["level_state"] == "blocked"
    assert l1_capsule["promotion_status"] == "l1-bounded-negative"
    assert owner["source_artifacts"]["construct_suspension_ref"] == {
        "artifact": "reports/canonical/dgt-l0-controls.json",
        "pointer": "$.construct_suspension",
    }
    assert owner["source_artifacts"]["interpretation_boundary_ref"] == {
        "artifact": "reports/canonical/fair-l1-decision.json",
        "pointer": "$.ladder_state_projection",
    }
    assert owner["source_artifacts"]["negative_witness_sweep_ref"] == {
        "artifact": "reports/canonical/dgt-l1-controls.json",
        "pointer": "$.negative_witness_sweep",
    }
    assert owner["source_artifacts"]["l1_ood_mechanism_ref"] == {
        "artifact": "reports/canonical/dgt-l1-controls.json",
        "pointer": "$.l1_ood_mechanism",
    }
    assert l1_capsule["l1_ood_mechanism_verdict_alias_source"] == "reports/canonical/dgt-l1-controls.json:$.l1_ood_mechanism.verdict"
    assert l1_capsule["l1_ood_mechanism_l2_implication_alias_source"] == "reports/canonical/dgt-l1-controls.json:$.l1_ood_mechanism.l2_implication"
    serialized = json.dumps(l1_capsule, sort_keys=True)
    for forbidden in ("metrics", "hardgates", "claim_capsule_ref", "discovery_map", "strata", "mechanism_scores", "stable_causal_attribution"):
        assert forbidden not in serialized
    assert "information_starved_baseline" not in serialized
    assert "hand_engineered_task_aligned_gate" not in serialized


@pytest.mark.parametrize("missing_key", ("negative_witness_sweep", "l1_ood_mechanism"))
def test_dgt_owner_refs_fail_closed_when_missing(tmp_path, missing_key):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    l1_path = tmp_path / "reports/canonical/dgt-l1-controls.json"
    l1_payload = json.loads(l1_path.read_text(encoding="utf-8"))
    l1_payload.pop(missing_key)
    l1_path.write_text(json.dumps(l1_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="owner refs"):
        dgt.build_payload(
            generated_at="fixture-time",
            high_impact_review_rows=_accepted_dgt_review_rows(),
            root=tmp_path,
        )


def test_dgt_owner_refs_fail_closed_when_all_owner_artifacts_are_absent(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)

    with pytest.raises(ValueError, match="owner refs"):
        dgt.build_payload(
            generated_at="fixture-time",
            high_impact_review_rows=_accepted_dgt_review_rows(),
            root=tmp_path,
        )


def test_dgt_promotion_reads_only_fair_l1_decision_projection(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    _write_passed_dgt_l0_controls_artifact(tmp_path)
    l1_payload = _write_ready_dgt_l1_controls_artifact(tmp_path)
    l1_path = tmp_path / "reports/canonical/dgt-l1-controls.json"
    mutated_l1 = json.loads(json.dumps(l1_payload))
    mutated_l1["discovery_map"] = {"verdict": "blocked"}
    mutated_l1["stable_causal_attribution"] = {"verdict": "blocked"}
    l1_path.write_text(json.dumps(mutated_l1, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )

    l1_capsule = owner["scaling_ladder"]["levels"][1]["claim_capsule"]
    assert l1_capsule["level_state"] == "blocked"
    assert l1_capsule["promotion_status"] == "l1-bounded-negative"

    _write_eligible_fair_l1_decision_artifact(tmp_path)
    eligible_owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    eligible_capsule = eligible_owner["scaling_ladder"]["levels"][1]["claim_capsule"]
    assert eligible_capsule["level_state"] == "ready"
    assert eligible_capsule["promotion_status"] == "l1-scaling-evidence-eligible"

    fair_path = tmp_path / fair_l1_decision.CANONICAL_JSON_ARTIFACT
    fair_payload = json.loads(fair_path.read_text(encoding="utf-8"))
    fair_payload["ladder_state_projection"]["state"] = "l1-scaling-blocked"
    fair_payload["ladder_state_projection"]["decision_status"] = "blocked"
    fair_path.write_text(json.dumps(fair_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    blocked_owner = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    blocked_capsule = blocked_owner["scaling_ladder"]["levels"][1]["claim_capsule"]
    assert blocked_capsule["level_state"] == "blocked"
    assert any(row["level_id"] == "L1_tiny_sequence" for row in blocked_owner["scaling_ladder"]["boundary_ledger"])


def test_dgt_scaling_ladder_missing_l0_pointer_keeps_l0_blocked(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    l0_payload = _write_passed_dgt_l0_controls_artifact(tmp_path)
    l0_path = tmp_path / "reports/canonical/dgt-l0-controls.json"
    l0_payload.pop("l0_toy_projection")
    l0_path.write_text(json.dumps(l0_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_ready_dgt_l1_controls_artifact(tmp_path)
    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    l0_capsule = payload["scaling_ladder"]["levels"][0]["claim_capsule"]

    assert l0_capsule["level_state"] == "suspended"
    assert l0_capsule["promotion_status"] == "suspended-by-l0-owner-pointer"
    assert l0_capsule["l0_toy_projection_ref"] == L0_TOY_PROJECTION_REF
    assert l0_capsule["ladder_consumption_ref"] is None
    assert l0_capsule["ladder_consumption_status"] == "suspended"
    assert payload["source_artifacts"]["ladder_consumption_ref"] is None
    assert payload["scaling_ladder"]["ladder_consumption_ref"] is None
    assert not any(key in l0_capsule for key in L0_FORBIDDEN_LADDER_KEYS)
    assert payload["scaling_ladder"]["boundary_ledger"][0]["level_id"] == "L0_toy"


def test_dgt_scaling_ladder_missing_l0_ladder_consumption_omits_source_ref(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    l0_payload = _write_passed_dgt_l0_controls_artifact(tmp_path)
    l0_path = tmp_path / "reports/canonical/dgt-l0-controls.json"
    l0_payload["l0_toy_projection"].pop("ladder_consumption", None)
    l0_path.write_text(json.dumps(l0_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_ready_dgt_l1_controls_artifact(tmp_path)

    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    l0_capsule = payload["scaling_ladder"]["levels"][0]["claim_capsule"]

    assert payload["source_artifacts"]["ladder_consumption_ref"] is None
    assert payload["scaling_ladder"]["ladder_consumption_ref"] is None
    assert l0_capsule["ladder_consumption_ref"] is None
    assert l0_capsule["level_state"] == "suspended"
    assert validate_scaling_ladder_projection(payload) == []


def test_dgt_owner_refs_reject_unresolved_ladder_consumption_pointer(tmp_path):
    _write_passed_dgt_neural_ablation_artifact(tmp_path)
    l0_payload = _write_passed_dgt_l0_controls_artifact(tmp_path)
    l0_path = tmp_path / "reports/canonical/dgt-l0-controls.json"
    l0_payload["l0_toy_projection"].pop("ladder_consumption", None)
    l0_path.write_text(json.dumps(l0_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_ready_dgt_l1_controls_artifact(tmp_path)

    payload = dgt.build_payload(
        generated_at="fixture-time",
        high_impact_review_rows=_accepted_dgt_review_rows(),
        root=tmp_path,
    )
    payload["source_artifacts"]["ladder_consumption_ref"] = dict(L0_LADDER_CONSUMPTION_REF)
    payload["scaling_ladder"]["ladder_consumption_ref"] = dict(L0_LADDER_CONSUMPTION_REF)
    payload["scaling_ladder"]["levels"][0]["claim_capsule"]["ladder_consumption_ref"] = dict(L0_LADDER_CONSUMPTION_REF)

    assert _owner_refs_resolve(tmp_path, payload) is False


def test_dgt_scaling_ladder_compute_param_ledger_is_strictly_monotone(tmp_path):
    owner = _owner_with_ready_scaling_ladder(tmp_path)
    ledgers = [
        row["claim_capsule"]["compute_param_ledger"]
        for row in owner["scaling_ladder"]["levels"]
        if row["level_id"] not in {"L0_toy", "L1_tiny_sequence"}
    ]

    assert [ledger["compute_units"] for ledger in ledgers] == sorted(ledger["compute_units"] for ledger in ledgers)
    assert [ledger["parameter_count"] for ledger in ledgers] == sorted(ledger["parameter_count"] for ledger in ledgers)


def test_dgt_scaling_ladder_boundary_tail_blocks_following_levels(tmp_path):
    owner = _owner_with_ready_scaling_ladder(tmp_path)
    mutated = json.loads(json.dumps(owner))
    mutated["scaling_ladder"]["levels"][2]["claim_capsule"]["level_state"] = "blocked"
    mutated["scaling_ladder"] = build_scaling_ladder_projection(mutated)

    boundary = mutated["scaling_ladder"]["boundary_ledger"]
    assert [row["level_id"] for row in boundary] == ["L2_char_lm", "L3_byte_lm", "L4_tool_use_toy", "L5_small_world_model"]
    assert boundary[0]["status"] == "failed"
    assert {row["status"] for row in boundary[1:]} == {"blocked"}


@pytest.mark.parametrize(
    ("gate_name", "mutate"),
    [
        ("DGT-ROB-HG1", lambda payload: payload["operational_robustness"].update({"owner_ref": f"{CANONICAL_JSON_ARTIFACT}:$"})),
        ("DGT-ROB-HG2", lambda payload: payload["operational_robustness"]["source_evidence"]["owner"].update({"d4_readiness": "blocked"})),
        ("DGT-ROB-HG3", lambda payload: payload["operational_robustness"]["source_evidence"]["owner"].update({"component_ablation_status": "fail"})),
        ("DGT-ROB-HG4", lambda payload: payload["operational_robustness"]["source_evidence"]["ledger_aware_transformer"].update({"robustness_status": "fail"})),
        ("DGT-ROB-HG5", lambda payload: payload["operational_robustness"]["source_evidence"]["model_comparison"].update({"hardgate_status": "fail"})),
        ("DGT-ROB-HG6", lambda payload: payload["operational_robustness"]["source_artifacts"].update({"ledger_aware_transformer_pointer": "reports/canonical/lat.json:$"})),
        ("DGT-ROB-HG7", lambda payload: payload["operational_robustness"].update({"not_claimed": []})),
        ("DGT-ROB-HG8", lambda payload: payload["operational_robustness"]["operational_contract"].update({"owner_policy": "production"})),
    ],
)
def test_dgt_robustness_hardgates_fail_closed(gate_name, mutate):
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutate(mutated)
    if gate_name == "DGT-ROB-HG8":
        mutated["operational_robustness"]["forbidden_claim_term_audit"] = {
            "status": "fail",
            "hits": ["operation authority wording"],
            "forbidden_terms": mutated["operational_robustness"]["forbidden_claim_term_audit"]["forbidden_terms"],
        }
    hardgate = evaluate_operational_robustness_hardgates(mutated["operational_robustness"])
    first_failed = hardgate["failed_gate"][0]
    mutated["operational_robustness"]["hardgate"] = hardgate
    mutated["operational_robustness"]["failed_gate"] = hardgate["failed_gate"]
    mutated["operational_robustness"]["failed_gate_pointer"] = f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness.hardgate.gates.{first_failed}"
    mutated["operational_robustness"]["status"] = "blocked"
    mutated["operational_robustness"]["readiness"] = "blocked"
    mutated["operational_robustness"]["discovery_level"] = "D0"

    assert hardgate["gates"][gate_name]["status"] == "fail"
    if gate_name == "DGT-ROB-HG1":
        with pytest.raises(ValueError, match="owner"):
            validate_operational_robustness(mutated["operational_robustness"], mutated)
        return
    validate_operational_robustness(mutated["operational_robustness"], mutated)
    assert mutated["operational_robustness"]["readiness"] == "blocked"
    assert mutated["operational_robustness"]["discovery_level"] == "D0"

    if gate_name == "DGT-ROB-HG8":
        with pytest.raises(ValueError, match="forbidden"):
            bad_token = json.loads(json.dumps(mutated["operational_robustness"]))
            bad_token["revocation_rows"].append({"gate": "DGT-ROB-HG8", "condition": "terminal_verdict"})
            validate_operational_robustness(bad_token, mutated)


def test_dgt_robustness_uses_lat_as_evidence_input_only():
    payload = dgt.build_payload(generated_at="fixture-time")
    robustness = payload["operational_robustness"]

    assert robustness["owner_ref"] == f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness"
    assert robustness["source_evidence"]["ledger_aware_transformer"]["source_role"] == "component-evidence-input"
    assert robustness["source_evidence"]["ledger_aware_transformer"]["level_candidate"] == "D5-O"
    assert robustness["operational_contract"]["lat_relationship"] == "LAT remains component evidence input only"
    assert "ledger-aware-transformer" not in robustness["owner_ref"]


def test_dgt_robustness_blocks_when_lat_source_evidence_not_ready():
    sources = default_robustness_source_payloads()
    sources["ledger_aware_transformer"]["robustness_signal"]["pass_surface_count"] = 2

    payload = dgt.build_payload(generated_at="fixture-time", robustness_source_payloads=sources)

    assert payload["operational_robustness"]["hardgate"]["gates"]["DGT-ROB-HG4"]["status"] == "fail"
    assert payload["operational_robustness"]["readiness"] == "blocked"
    assert payload["operational_robustness"]["discovery_level"] == "D0"


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
    robustness_nonclaims = " ".join(payload["operational_robustness"]["not_claimed"]).lower()

    assert "global superiority" not in nonclaims
    assert "production" not in nonclaims
    assert "global superiority" not in robustness_nonclaims
    assert "production" not in robustness_nonclaims
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"


def test_dgt_rejects_inline_source_metric_bodies():
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutated["component_refs"]["metric_body"] = {"artifact": "x", "pointer": "$", "records": []}

    with pytest.raises(ValueError, match="inline source body"):
        validate_projection(mutated)


def test_dgt_d5_m_neural_ablation_fails_closed_without_new_owner(tmp_path):
    _write_required_dgt_external_artifacts(tmp_path)
    _write_dgt_owner_refs(tmp_path)
    (tmp_path / "reports" / "canonical" / "dgt-neural-ablation.json").write_text(
        json.dumps({"nabl_hardgates": {"status": "fail", "failed_gate": "NABL-HG2"}}) + "\n",
        encoding="utf-8",
    )

    payload = dgt.build_payload(generated_at="fixture-time", root=tmp_path)

    assert payload["component_ablation"]["hardgate"]["status"] == "pass"
    assert payload["neural_ablation_ref"] == {
        "artifact": "reports/canonical/dgt-neural-ablation.json",
        "pointer": "$.nabl_hardgates.failed_gate",
    }
    assert payload["d5_m_projection"]["hardgates"]["D5M-HG6"]["status"] == "fail"
    assert payload["d5_m_projection"]["status"] == "blocked"


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
