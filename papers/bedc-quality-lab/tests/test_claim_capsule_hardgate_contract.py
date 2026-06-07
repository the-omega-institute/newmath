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
