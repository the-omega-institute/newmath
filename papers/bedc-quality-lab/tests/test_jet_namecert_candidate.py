import dataclasses
import json

import bedc_quality_lab
from bedc_quality_lab.jet_namecert_candidate import (
    DGT_JSON_ARTIFACT,
    DGT_PROJECTION_SCHEMA_ID,
    MARKDOWN_ARTIFACT,
    OWNER_JSON_ARTIFACT,
    SCHEMA_ID,
    JetNameCertCandidate,
    audit_dgt_jet_projection,
    audit_jet_namecert_candidate,
    build_dgt_jet_projection,
    closure_status_rows,
    payload_sha256,
    render_boundary_causal_jet_certificate,
)
from scripts import run_jet_namecert_candidate as runner


def _payload(**overrides):
    payload = JetNameCertCandidate.from_sources(
        generated_at="fixture-time",
        dgt_payload={"schema_id": "bedc-quality-lab:discovery-gated-transformer", "artifact_id": "dgt", "generated_at": "fixture-time"},
        jet_certificate_payload={"schema_id": "bedc-quality-lab:dgt-jet-certificate", "artifact_id": "jet", "generated_at": "fixture-time"},
        derivative_payload={"schema_id": "bedc-quality-lab:transformer-derivative-atlas", "artifact_id": "atlas", "generated_at": "fixture-time"},
        causal_patch_payload={"schema_id": "bedc-quality-lab:causal-patch-suite", "artifact_id": "patch", "generated_at": "fixture-time"},
        attribution_payload={"schema_id": "bedc-quality-lab:gap-head-attribution-capsule", "artifact_id": "a1", "generated_at": "fixture-time"},
    ).to_dict()
    payload.update(overrides)
    if overrides:
        payload["audit"] = audit_jet_namecert_candidate(payload)
    return payload


def test_exact_field_shape_json_ready_and_package_local():
    candidate = JetNameCertCandidate.from_sources(generated_at="fixture-time")

    assert [field.name for field in dataclasses.fields(JetNameCertCandidate)] == [
        "schema_id",
        "artifact_id",
        "generated_at",
        "name",
        "json_artifact",
        "dgt_projection_artifact",
        "markdown_artifact",
        "source_artifacts",
        "boundary_spec",
        "derivative_spec",
        "irreducibility_spec",
        "causal_patch_spec",
        "stability_spec",
        "ledger_policy",
        "scope",
        "closure_status",
        "audit",
    ]
    payload = candidate.to_dict()
    encoded = json.dumps(payload, sort_keys=True)

    assert payload["schema_id"] == SCHEMA_ID
    assert payload["json_artifact"] == OWNER_JSON_ARTIFACT
    assert "JetNameCertCandidate:boundary-causal-jet" in encoded
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert not hasattr(bedc_quality_lab, "JetNameCertCandidate")
    assert payload["scope"] == {
        "semantics": "lab-local JetNameCertCandidate",
        "formal_bedc_namecert": False,
        "lean_verification": False,
        "paper_closurestatus": False,
        "d5_m_claim": False,
        "canonical_report": False,
        "not_claimed": [
            "not a formal BEDC NameCert",
            "not Lean verification",
            "not a paper closurestatus",
            "not a canonical report",
        ],
    }


def test_each_claimed_order_requires_evidence_pointer():
    payload = _payload()
    payload["derivative_spec"]["claimed_orders"][0]["evidence_pointer"] = None
    payload["closure_status"]["derivative_spec"] = "open"
    payload["closure_status"]["overall"] = "open"

    audit = audit_jet_namecert_candidate(payload)

    assert audit["hardgates"]["JETCERT-HG1"]["status"] == "fail"
    assert "$.derivative_spec.claimed_orders[0].evidence_pointer" in audit["hardgates"]["JETCERT-HG1"]["blockers"]
    assert audit["d5_m_ready"] is False


def test_causal_order_requires_patch_pointer():
    payload = _payload()
    payload["causal_patch_spec"]["claimed_orders"][0]["patch_pointer"] = ""
    payload["closure_status"]["causal_patch_spec"] = "open"
    payload["closure_status"]["overall"] = "open"

    audit = audit_jet_namecert_candidate(payload)

    assert audit["hardgates"]["JETCERT-HG2"]["status"] == "fail"
    assert "$.causal_patch_spec.claimed_orders[0].patch_pointer" in audit["hardgates"]["JETCERT-HG2"]["blockers"]
    assert audit["d5_m_ready"] is False


def test_irreducible_order_requires_low_order_baseline():
    payload = _payload()
    payload["irreducibility_spec"]["claimed_orders"][0]["low_order_baseline_pointer"] = None
    payload["closure_status"]["irreducibility_spec"] = "open"
    payload["closure_status"]["overall"] = "open"

    audit = audit_jet_namecert_candidate(payload)

    assert audit["hardgates"]["JETCERT-HG3"]["status"] == "fail"
    assert "$.irreducibility_spec.claimed_orders[0].low_order_baseline_pointer" in audit["hardgates"]["JETCERT-HG3"]["blockers"]
    assert audit["d5_m_ready"] is False


def test_open_closure_blocks_d5_m():
    payload = JetNameCertCandidate.from_sources(generated_at="fixture-time").to_dict()

    audit = audit_jet_namecert_candidate(payload)

    assert payload["closure_status"]["overall"] == "open"
    assert audit["hardgates"]["JETCERT-HG4"]["status"] == "fail"
    assert audit["d5_m_ready"] is False
    payload["scope"]["d5_m_claim"] = True
    assert "scope.d5_m_claim" in audit_jet_namecert_candidate(payload)["failures"]


def test_closure_status_rows():
    candidate = JetNameCertCandidate.from_sources(generated_at="fixture-time")

    rows = closure_status_rows(candidate)
    row_map = {row["field"]: row for row in rows}
    expected_fields = {field.name for field in dataclasses.fields(JetNameCertCandidate) if field.name not in {"substitution"}}

    assert set(row_map) == expected_fields
    assert len(rows) == len(row_map)
    for field in (
        "boundary_spec",
        "derivative_spec",
        "irreducibility_spec",
        "causal_patch_spec",
        "stability_spec",
        "ledger_policy",
        "scope",
    ):
        assert row_map[field]["status"] == candidate.closure_status[field]
        assert row_map[field]["pointer"] == f"$.{field}"
    assert row_map["schema_id"]["status"] == "present"
    assert row_map["closure_status"]["status"] == candidate.closure_status["overall"]
    assert row_map["closure_status"]["pointer"] == "$.closure_status"
    assert row_map["audit"]["status"] == candidate.audit["status"]
    assert row_map["audit"]["pointer"] == "$.audit"


def test_dgt_and_markdown_are_owner_projections():
    owner = _payload()
    projection = build_dgt_jet_projection(owner)
    markdown = render_boundary_causal_jet_certificate(owner)

    assert projection["schema_id"] == DGT_PROJECTION_SCHEMA_ID
    assert projection["owner_artifact"] == OWNER_JSON_ARTIFACT
    assert projection["owner_sha256"] == payload_sha256(owner)
    assert set(projection) == {
        "schema_id",
        "artifact_id",
        "generated_at",
        "projection_role",
        "owner_artifact",
        "owner_sha256",
        "hardgate_pointers",
        "render_metadata",
    }
    lowered = json.dumps(projection, sort_keys=True)
    for forbidden in (
        "boundary_spec",
        "derivative_spec",
        "irreducibility_spec",
        "causal_patch_spec",
        "stability_spec",
        "ledger_policy",
        "closure_status",
        "d5_m_ready",
    ):
        assert forbidden not in lowered
    assert audit_dgt_jet_projection({**projection, "boundary_spec": {}})["status"] == "fail"
    assert OWNER_JSON_ARTIFACT in markdown
    assert payload_sha256(owner) in markdown
    assert "boundary-order" not in markdown


def test_runner_writes_three_named_artifacts_from_one_payload(tmp_path):
    _write_sources(tmp_path)

    owner = runner.write_jet_namecert_candidate(root=tmp_path, generated_at="fixture-time")

    owner_path = tmp_path / OWNER_JSON_ARTIFACT
    dgt_path = tmp_path / DGT_JSON_ARTIFACT
    markdown_path = tmp_path / MARKDOWN_ARTIFACT
    assert owner_path.exists()
    assert dgt_path.exists()
    assert markdown_path.exists()
    written_owner = json.loads(owner_path.read_text(encoding="utf-8"))
    projection = json.loads(dgt_path.read_text(encoding="utf-8"))
    markdown = markdown_path.read_text(encoding="utf-8")

    assert owner == written_owner
    assert written_owner["audit"]["d5_m_ready"] is True
    assert written_owner["scope"]["d5_m_claim"] is True
    assert projection["owner_artifact"] == OWNER_JSON_ARTIFACT
    assert projection["owner_sha256"] == payload_sha256(written_owner)
    assert payload_sha256(written_owner) in markdown


def _write_sources(root):
    for artifact, schema_id, artifact_id in (
        (runner.DGT_CANONICAL_ARTIFACT, "bedc-quality-lab:discovery-gated-transformer", "dgt"),
        (runner.DGT_RUN_JET_CERTIFICATE_ARTIFACT, "bedc-quality-lab:dgt-jet-certificate", "jet"),
        (runner.TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT, "bedc-quality-lab:transformer-derivative-atlas", "atlas"),
        (runner.CAUSAL_PATCH_SUITE_ARTIFACT, "bedc-quality-lab:causal-patch-suite", "patch"),
        (runner.GAP_HEAD_ATTRIBUTION_ARTIFACT, "bedc-quality-lab:gap-head-attribution-capsule", "a1"),
    ):
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {
                    "schema_id": schema_id,
                    "artifact_id": artifact_id,
                    "generated_at": "fixture-time",
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
