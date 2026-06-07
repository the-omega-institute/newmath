from __future__ import annotations

import json

from bedc_quality_lab.discovery_compiler.hardgate_contract import evaluate_u_hardgates


def _write_json(path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _payload():
    return {
        "self_artifact": "reports/runs/fixture/claim_capsule.json",
        "claim_status": "failed",
        "positive_claim": {"text": "fixture audit improvement", "level": "DN"},
        "source_artifacts": {"cost_protocol": "configs/default_cost_protocol.yaml"},
        "cost_protocol": {"artifact": "configs/default_cost_protocol.yaml"},
        "evidence_pointers": ["reports/runs/fixture/claim_capsule.json:$.positive_claim"],
        "not_claimed": ["full LeJEPA", "global model quality"],
        "control_rows": [{"control": "matched", "status": "present"}],
        "failed_gate": "D2-HG2",
        "what_was_learned": "fixture negative learning",
        "revocation": {"rows": [{"condition": "fixture", "status": "armed"}]},
    }


def test_contract_passes_resolvable_owner_local_capsule_pointer(tmp_path):
    payload = _payload()

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA", "global model quality"),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["status"] == "pass"
    assert result["gates"]["U-HG1"]["status"] == "pass"
    assert result["gates"]["U-HG2"]["status"] == "pass"


def test_contract_fails_dangling_evidence_pointer(tmp_path):
    payload = {**_payload(), "evidence_pointers": ["reports/runs/fixture/missing.json:$.x"]}
    _write_json(tmp_path / "reports/runs/fixture/claim_capsule.json", payload)

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA",),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["gates"]["U-HG2"]["status"] == "fail"


def test_contract_enforces_not_claimed_terms(tmp_path):
    payload = _payload()

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA", "full TensorNameCert"),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["gates"]["U-HG4"]["status"] == "fail"
    assert result["gates"]["U-HG4"]["missing"] == ["full TensorNameCert"]


def test_contract_fails_closed_for_missing_cost_pointer(tmp_path):
    payload = {**_payload(), "cost_protocol": {}}

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA",),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["status"] == "fail"
    assert result["failed_gates"] == ["U-HG3"]
    assert result["gates"]["U-HG3"]["status"] == "fail"
    assert result["gates"]["U-HG3"]["cost_pointer"] == "$.cost_protocol.artifact"


def test_contract_fails_closed_for_missing_required_control_rows(tmp_path):
    payload = {**_payload(), "control_rows": []}

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA",),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["status"] == "fail"
    assert result["failed_gates"] == ["U-HG5"]
    assert result["gates"]["U-HG5"] == {
        "status": "fail",
        "control_required": True,
        "control_row_count": 0,
    }


def test_contract_forbidden_positive_claim_terms_fail(tmp_path):
    payload = {**_payload(), "positive_claim": {"text": "global-quality", "level": "DN"}}

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA",),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["gates"]["U-HG8"]["status"] == "fail"
    assert result["gates"]["U-HG8"]["positive_claim_audit"]["hits"]


def test_contract_forbidden_public_surface_columns_fail_closed(tmp_path):
    forbidden_payload = {
        "terminal_verdict": "positive",
        "positive_claim": {"text": "fixture"},
        "arm_aggregates": [],
        "metrics": {},
    }
    payload = {**_payload(), "public_surface": forbidden_payload}

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA",),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    audit = result["gates"]["U-HG8"]["forbidden_column_audit"]
    assert result["status"] == "fail"
    assert result["failed_gates"] == ["U-HG8"]
    assert result["gates"]["U-HG8"]["status"] == "fail"
    assert audit["status"] == "fail"
    assert audit["hits"] == ["terminal_verdict", "positive_claim", "arm_aggregates", "metrics"]


def test_contract_dn_requires_failed_gate_and_learning(tmp_path):
    payload = {**_payload(), "failed_gate": None}

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA",),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["gates"]["U-HG6"]["status"] == "fail"


def test_contract_dr_requires_revocation_rows(tmp_path):
    payload = {**_payload(), "revocation": {"rows": []}}

    result = evaluate_u_hardgates(
        payload,
        root=tmp_path,
        capsule_artifact="reports/runs/fixture/claim_capsule.json",
        required_not_claimed=("full LeJEPA",),
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )

    assert result["gates"]["U-HG7"]["status"] == "fail"
