import json
from copy import deepcopy

import pytest

from bedc_quality_lab.discovery_compiler.capsule import (
    ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
    CLAIM_CAPSULE_SCHEMA_ID,
    build_architecture_claim_capsule_payload,
    require_architecture_claim_capsule,
)
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from scripts import run_canonical_reports as canonical

EXPECTED_MODEL_DESIGN_COMPONENTS = {
    "bedc-quality-lab:ledger-aware-transformer",
    "bedc-quality-lab:certificate-gated-attention",
    "bedc-quality-lab:discovery-regularized-training",
    "bedc-quality-lab:mechanism-seeking-network",
    canonical.DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID,
}
EXPECTED_MODEL_DESIGN_OWNER_ARTIFACTS = {
    "reports/canonical/ledger-aware-transformer.json",
    "reports/canonical/certificate-gated-attention.json",
    canonical.DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT,
    canonical.MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT,
    canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
}


def _model_claim() -> dict:
    return {
        "model_id": "design-suite-canonical-projection",
        "claim": "fixture model architecture claim",
        "baselines": [{"artifact": canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT, "pointer": "$.training_replay_ref"}],
        "forbidden_evidence": ["test_label"],
        "required_gates": ["SUITE-HG1", "SUITE-HG2", "SUITE-HG3"],
        "candidate_pointer": {"artifact": canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT, "pointer": "$.rows"},
        "evidence_pointer": {"artifact": canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT, "pointer": "$.hardgates"},
    }


def test_architecture_claim_capsule_uses_quality_schema_and_capsule_subtype():
    payload = build_architecture_claim_capsule_payload(
        generated_at="fixture-time",
        claim_id="claim:model",
        report="model-design-suite",
        source_artifact=canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT,
        source_pointer="$.rows",
        model_claim=_model_claim(),
    )

    capsule = require_architecture_claim_capsule(payload)

    assert capsule.payload["schema_id"] == CLAIM_CAPSULE_SCHEMA_ID
    assert capsule.payload["capsule_subtype"] == ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE
    assert "capsule_role" not in capsule.payload


@pytest.mark.parametrize(
    ("mutation", "match"),
    [
        ({"capsule_subtype": None}, "capsule_subtype"),
        ({"capsule_subtype": "bedc.model.architecture_claim_capsulee"}, "capsule_subtype"),
        ({"schema_id": "bedc.model.architecture_claim_capsule"}, "schema_id"),
        ({"capsule_subtype": None, "capsule_role": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE}, "capsule_subtype"),
        ({"architecture_claim_capsule_schema_id": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE}, "architecture_claim_capsule_schema_id"),
    ],
)
def test_architecture_claim_capsule_rejects_marker_mistakes(mutation, match):
    payload = build_architecture_claim_capsule_payload(
        generated_at="fixture-time",
        claim_id="claim:model",
        report="model-design-suite",
        source_artifact=canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT,
        source_pointer="$.rows",
        model_claim=_model_claim(),
    )
    payload.update(mutation)

    with pytest.raises(ValueError, match=match):
        require_architecture_claim_capsule(payload)


def test_architecture_claim_capsule_rejects_missing_model_claim_cells():
    with pytest.raises(ValueError, match="model_claim cells"):
        build_architecture_claim_capsule_payload(
            generated_at="fixture-time",
            claim_id="claim:model",
            report="model-design-suite",
            source_artifact=canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT,
            source_pointer="$.rows",
            model_claim={"model_id": "toy-design-suite"},
        )


def _write_dgt_owner_ref_fixtures(root) -> None:
    canonical._write_json_atomic(
        root / canonical.DGT_L0_CONTROLS_JSON_ARTIFACT,
        {
            "construct_suspension": {"status": "fixture"},
            "negative_witness_sweep": {"status": "fixture"},
            "l0_toy_projection": {
                "status": "pass",
                "review_status": "pass",
                "hardgate_statuses": {"pass": {"status": "pass"}},
                "not_claimed": ["fixture"],
            },
        },
    )
    canonical._write_json_atomic(
        root / canonical.DGT_L1_CONTROLS_JSON_ARTIFACT,
        {
            "l1_tiny_sequence_projection": {
                "status": "pass",
                "review_status": "pass",
                "promotion_readiness": "ready-pass",
                "not_claimed": ["fixture"],
            },
            "negative_witness_sweep": {"status": "pass"},
            "l1_ood_mechanism": {
                "verdict": "fixture",
                "l2_implication": "not-claimed",
            },
            "l1_step_ladder": {
                "convergence_crossover": {"status": "fixture"},
                "verdict": "construct-boundary",
                "hardgates": {"BASE-UNDER-HG0": {"status": "fail-closed"}},
                "not_claimed": ["fixture"],
            },
        },
    )


def _write_suite_dependencies(root):
    _write_dgt_owner_ref_fixtures(root)
    dgt = canonical._build_discovery_gated_transformer_payload(generated_at="fixture-time")
    canonical._write_json_atomic(root / canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT, dgt)
    canonical._write_json_atomic(
        root / canonical.DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT,
        {
            "artifact_id": "bedc-quality-lab:discovery-regularized-training",
            "torch_training_evidence": {"status": "available"},
            "training_mechanism_cert": {"status": "pass"},
            "quality_promotion_boundary": {
                "hardgate": {"status": "present-but-fail-closed"},
            }
        },
    )
    canonical._write_json_atomic(
        root / canonical.DISCOVERY_MAP_JSON_ARTIFACT,
        {"coverage_matrix": {"status": "pointer-only"}, "level_counts": {"D0": 0}},
    )
    canonical._write_json_atomic(
        root / canonical.DGT_NEURAL_ABLATION_JSON_ARTIFACT,
        {"nabl_hardgates": {"status": "pass"}},
    )
    canonical._write_json_atomic(root / canonical.NEGATIVE_WITNESSES_JSON_ARTIFACT, {"witnesses": [{"kind": "fixture"}]})
    canonical._write_json_atomic(
        root / canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT,
        {"entries": [{"mutation_id": f"m{index}"} for index in range(8)]},
    )
    _write_dgt_owner_ref_fixtures(root)
    canonical._write_json_atomic(
        root / canonical.DGT_NEURAL_ABLATION_JSON_ARTIFACT,
        {"nabl_hardgates": {"status": "fixture"}},
    )
    canonical._write_json_atomic(
        root / "reports/canonical/ledger-aware-transformer.json",
        {"artifact_id": "bedc-quality-lab:ledger-aware-transformer", "run_artifacts": {"summary": "fixture"}},
    )
    canonical._write_json_atomic(
        root / "reports/canonical/certificate-gated-attention.json",
        {"artifact_id": "bedc-quality-lab:certificate-gated-attention", "certificate_gate_summary": {"status": "fixture"}},
    )
    canonical._write_json_atomic(
        root / canonical.GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT,
        {"ledger_debt": [{"status": "open"}], "mechanism_evidence": {"status": "blocked"}},
    )
    canonical._write_json_atomic(
        root / canonical.MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT,
        {
            "artifact_id": "bedc-quality-lab:mechanism-seeking-network",
            "discovery_map_signal": {"status": "available"},
            "hardgate": {"status": "pass"},
            "mechanism_gate_summary": {"status": "available"},
            "revocation_rows": [{"status": "none"}],
            "not_claimed": ["fixture"],
        },
    )


def _payload_with_root(tmp_path):
    original_root = canonical.ROOT
    original_dir = canonical.CANONICAL_DIR
    try:
        canonical.ROOT = tmp_path
        canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
        _write_suite_dependencies(tmp_path)
        payload = canonical._build_model_design_suite_payload(generated_at="fixture-time")
        canonical._write_json_atomic(tmp_path / canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT, payload)
        return payload
    finally:
        canonical.ROOT = original_root
        canonical.CANONICAL_DIR = original_dir


def test_model_design_suite_is_runner_local_pointer_only_and_resolvable(tmp_path):
    payload = _payload_with_root(tmp_path)

    assert payload["schema_id"] == canonical.MODEL_DESIGN_SUITE_SCHEMA_ID
    assert payload["status"] == "pass"
    assert payload["canonical_owner"]["owner_pointer"] == f"{canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT}:$"
    assert {gate["status"] for gate in payload["hardgates"].values()} == {"pass"}
    assert all(set(row) == canonical.MODEL_DESIGN_SUITE_ROW_FIELDS for row in payload["rows"])
    assert "terminal_verdict" not in json.dumps(payload, sort_keys=True)
    assert "candidate_measurements" not in json.dumps(payload, sort_keys=True)

    for row in payload["rows"]:
        for field in canonical.MODEL_DESIGN_SUITE_POINTER_FIELDS:
            assert resolve_artifact_pointer(tmp_path, row[field]) is not None, (field, row[field])
    assert {
        row["negative_witness_pointer"]
        for row in payload["rows"]
        if canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT in row["negative_witness_pointer"]
        } == {
            f"{canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries",
            f"{canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries[3]",
            f"{canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries[6]",
            f"{canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries[7]",
    }


def test_model_design_suite_dgt_row_uses_canonical_owner_artifact(tmp_path):
    payload = _payload_with_root(tmp_path)

    by_component = {
        (
            resolved
            if isinstance((resolved := resolve_artifact_pointer(tmp_path, row["component_id"])), str)
            else resolved["role"]
        ): row
        for row in payload["rows"]
    }
    dgt = by_component[canonical.DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID]
    owner = resolve_artifact_pointer(tmp_path, dgt["canonical_owner_pointer"])

    assert dgt["canonical_owner_pointer"] == f"{canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$"
    assert owner["artifact_id"] == canonical.DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID
    assert owner["model_id"] == "discovery-gated-transformer"


def test_model_design_suite_committed_json_round_trip_checks_slot_set(tmp_path):
    payload = _payload_with_root(tmp_path)

    original_root = canonical.ROOT
    original_dir = canonical.CANONICAL_DIR
    try:
        canonical.ROOT = tmp_path
        canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
        canonical._validate_committed_model_design_suite_round_trip()
    finally:
        canonical.ROOT = original_root
        canonical.CANONICAL_DIR = original_dir

    components = set()
    owner_artifacts = set()
    for row in payload["rows"]:
        resolved = resolve_artifact_pointer(tmp_path, row["component_id"])
        components.add(resolved if isinstance(resolved, str) else resolved["role"])
        owner_artifacts.add(row["canonical_owner_pointer"].split(":", 1)[0])
    assert components == EXPECTED_MODEL_DESIGN_COMPONENTS
    assert owner_artifacts == EXPECTED_MODEL_DESIGN_OWNER_ARTIFACTS
    assert len(payload["rows"]) == len(EXPECTED_MODEL_DESIGN_COMPONENTS)


def test_model_design_suite_msn_row_is_pointer_only(tmp_path):
    payload = _payload_with_root(tmp_path)
    msn_row = next(
        row
        for row in payload["rows"]
        if row["component_id"] == f"{canonical.MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.artifact_id"
    )

    assert msn_row["canonical_owner_pointer"] == f"{canonical.MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$"
    assert msn_row["discovery_pointer"] == f"{canonical.MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.discovery_map_signal"
    assert msn_row["mechanism_pointer"] == f"{canonical.MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.mechanism_gate_summary"
    assert "surface_atlas" not in json.dumps(payload, sort_keys=True)
    assert "surface_registry" not in json.dumps(msn_row, sort_keys=True)
    assert "by_mechanism" not in json.dumps(msn_row, sort_keys=True)


@pytest.mark.parametrize(
    ("field", "value", "reason"),
    [
        ("canonical_owner_pointer", None, "missing pointer fields: canonical_owner_pointer"),
        ("canonical_owner_pointer", "", "missing pointer fields: canonical_owner_pointer"),
        ("canonical_owner_pointer", "reports/canonical/model_design_suite.json:$.missing", "dangling pointer fields: canonical_owner_pointer"),
    ],
)
def test_suite_hg2_owner_pointer_fail_closed_and_propagates(tmp_path, field, value, reason):
    payload = _payload_with_root(tmp_path)
    mutated = deepcopy(payload)
    mutated["rows"][1][field] = value
    if field == "canonical_owner_pointer" and isinstance(value, str) and value:
        mutated["rows"][1]["discovery_pointer"] = f"{canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT}:$.rows[0]"
        mutated["rows"][1]["verdict_pointer"] = f"{canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT}:$.rows[0]"
    mutated["rows"][1]["hardgate_status"], mutated["rows"][1]["hardgate_reason"] = (
        canonical._model_design_suite_row_status(mutated["rows"][1], payload=mutated)
    )
    mutated["hardgates"] = canonical._model_design_suite_hardgate_rows(mutated["rows"])
    mutated["status"] = "fail"

    canonical._validate_model_design_suite_payload(mutated)

    assert mutated["rows"][1]["hardgate_status"] == "fail"
    assert mutated["rows"][1]["hardgate_reason"] == reason
    assert mutated["hardgates"]["SUITE-HG2"]["status"] == "fail"
    assert mutated["hardgates"]["SUITE-HG5"]["status"] == "fail"
    assert mutated["status"] == "fail"


@pytest.mark.parametrize(
    ("gate_id", "field"),
    [
        ("SUITE-HG1", "component_id"),
        ("SUITE-HG2", "canonical_owner_pointer"),
        ("SUITE-HG3", "discovery_pointer"),
        ("SUITE-HG4", "verdict_pointer"),
        ("SUITE-HG5", "negative_witness_pointer"),
    ],
)
def test_each_suite_hardgate_negative_fixture_fails_closed(tmp_path, gate_id, field):
    payload = _payload_with_root(tmp_path)
    mutated = deepcopy(payload)
    mutated["rows"][0][field] = f"{canonical.MODEL_DESIGN_SUITE_JSON_ARTIFACT}:$.missing_{field}"
    mutated["rows"][0]["hardgate_status"], mutated["rows"][0]["hardgate_reason"] = (
        canonical._model_design_suite_row_status(mutated["rows"][0], payload=mutated)
    )
    mutated["hardgates"] = canonical._model_design_suite_hardgate_rows(mutated["rows"])
    mutated["status"] = "fail"

    canonical._validate_model_design_suite_payload(mutated)

    assert mutated["rows"][0]["hardgate_status"] == "fail"
    assert mutated["hardgates"][gate_id]["status"] == "fail"
    assert mutated["hardgates"]["SUITE-HG5"]["status"] == "fail"
    assert mutated["status"] == "fail"


@pytest.mark.parametrize(
    "mutation",
    [
        lambda payload: payload["rows"][0].__setitem__("terminal_verdict", "accepted"),
        lambda payload: payload["rows"][0].__setitem__("host", {"env": {"TOKEN": "x"}}),
        lambda payload: payload["rows"][0].__setitem__("candidate_evidence_body", {"score": 1.0}),
    ],
)
def test_model_design_suite_recursive_forbidden_key_validator_rejects_row_bodies(tmp_path, mutation):
    payload = _payload_with_root(tmp_path)
    mutated = deepcopy(payload)
    mutation(mutated)

    with pytest.raises(ValueError, match="forbidden keys"):
        canonical._validate_model_design_suite_payload(mutated)
