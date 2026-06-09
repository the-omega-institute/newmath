import json

import pytest

from bedc_quality_lab import dgt_neural_ablation as owner
from scripts import run_dgt_neural_ablation as runner


def test_registry_has_exact_arms_and_metrics():
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")

    assert tuple(payload["module_registry"]) == owner.ARM_IDS
    assert len(payload["records"]) == 11
    assert [row["arm_id"] for row in payload["records"]] == list(owner.ARM_IDS)
    for row in payload["records"]:
        assert set(row["metrics"]) == set(owner.METRIC_KEYS)
        assert row["requested_training_backend"] == "torch"
        assert row["optimizer_steps"] > 0
        assert row["parameter_l2_delta"] > 0.0


def test_nabl_hardgates_and_hg7_boundary_fail_closed():
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")

    owner.validate_payload(payload)
    assert payload["nabl_hardgates"]["status"] == "pass"
    assert set(payload["nabl_hardgates"]["gates"]) == set(owner.HG_IDS)
    blocked = [row for row in payload["boundary_ledger"] if row["claim_blocked"]]
    assert blocked == [
        {
            "claim_blocked": True,
            "component": "scope_seal",
            "metric_delta_pointer": "reports/canonical/dgt-neural-ablation.json:$.metric_delta_matrix.DGT_without_scope_seal",
            "reason": "HG7 boundary: no measurable effect; component-causal claim blocked",
            "status": "no_measurable_effect",
        }
    ]
    claimed = {row["component"] for row in payload["component_causal_claims"]}
    assert "scope_seal" not in claimed
    assert {
        tuple(row["evidence_scope"])
        for row in payload["component_causal_claims"]
        if row["claim_status"] == "allowed"
    } == {("small-real-training",)}


def test_unavailable_payload_has_no_positive_component_claim():
    payload = owner.unavailable_payload(generated_at="fixture", requested_device="auto", reason="torch unavailable")

    owner.validate_payload(payload)
    assert payload["training_protocol"]["status"] == "unavailable"
    assert payload["nabl_hardgates"]["status"] == "fail"
    assert payload["component_causal_claims"] == []


def test_forbidden_positive_claim_terms_are_audited():
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")
    mutated = json.loads(json.dumps(payload))
    mutated["component_causal_claims"][0]["claim_text"] = "global superiority"
    mutated["forbidden_claim_term_audit"] = owner._forbidden_claim_term_audit(
        {"claims": mutated["component_causal_claims"]}
    )

    with pytest.raises(ValueError, match="forbidden term audit"):
        owner.validate_payload(mutated)


@pytest.mark.parametrize(
    "evidence_scope",
    [
        None,
        "small-real-training",
        [],
        ["small-real-training", "small-real-training"],
        ["outside-enum"],
    ],
)
def test_component_causal_claim_rejects_invalid_evidence_scope(evidence_scope):
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")
    mutated = json.loads(json.dumps(payload))
    mutated["component_causal_claims"][0]["evidence_scope"] = evidence_scope

    with pytest.raises(ValueError, match="component claim 0 evidence_scope"):
        owner.validate_payload(mutated)


def test_write_artifacts_emits_canonical_run_capsule_report_metrics_and_fingerprint(tmp_path):
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")

    owner.write_artifacts(payload, root=tmp_path, generated_at="fixture")

    emitted = [
        owner.CANONICAL_JSON_ARTIFACT,
        owner.CANONICAL_MARKDOWN_ARTIFACT,
        owner.CANONICAL_FINGERPRINT_ARTIFACT,
        payload["run_artifacts"]["summary"],
        payload["run_artifacts"]["raw_metrics"],
        payload["run_artifacts"]["claim_capsule"],
        payload["run_artifacts"]["report"],
    ]
    assert all((tmp_path / artifact).exists() for artifact in emitted)

    capsule = json.loads((tmp_path / payload["run_artifacts"]["claim_capsule"]).read_text(encoding="utf-8"))
    assert capsule["owner_pointer"] == f"{owner.CANONICAL_JSON_ARTIFACT}:$"
    assert capsule["hardgate_pointer"] == f"{owner.CANONICAL_JSON_ARTIFACT}:$.nabl_hardgates.status"
    assert capsule["component_claim_pointer"] == f"{owner.CANONICAL_JSON_ARTIFACT}:$.component_causal_claims"
    assert capsule["claim_count"] == len(payload["component_causal_claims"])

    raw_rows = (tmp_path / payload["run_artifacts"]["raw_metrics"]).read_text(encoding="utf-8").splitlines()
    assert len(raw_rows) == len(payload["records"])
    assert json.loads(raw_rows[0])["arm_id"] == owner.ARM_IDS[0]

    markdown = (tmp_path / owner.CANONICAL_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    assert "# DGT neural ablation" in markdown
    assert "- Status: `pass`" in markdown
    assert f"- Claim capsule: `{payload['claim_capsule_ref']['artifact']}:$`" in markdown

    fingerprint = json.loads((tmp_path / owner.CANONICAL_FINGERPRINT_ARTIFACT).read_text(encoding="utf-8"))
    assert fingerprint["report_name"] == "dgt-neural-ablation"
    assert len(fingerprint["input_fingerprint"]) == 64
    assert len(fingerprint["output_digest"]) == 64
    assert fingerprint["generated_by"]["generated_at"] == "fixture"


def test_cli_main_writes_cpu_artifact_layout(tmp_path, capsys):
    exit_code = runner.main(["--root", str(tmp_path), "--generated-at", "fixture", "--requested-device", "cpu"])

    assert exit_code == 0
    summary = json.loads(capsys.readouterr().out)
    assert summary["artifact_id"] == owner.ARTIFACT_ID
    assert summary["status"] == "pass"
    assert summary["device"] == "cpu"
    assert summary["arm_count"] == len(owner.ARM_IDS)
    assert summary["claim_count"] == len(owner.build_payload(generated_at="fixture", requested_device="cpu")["component_causal_claims"])

    assert (tmp_path / owner.CANONICAL_JSON_ARTIFACT).exists()
    assert (tmp_path / owner.CANONICAL_MARKDOWN_ARTIFACT).exists()
    assert (tmp_path / owner.CANONICAL_FINGERPRINT_ARTIFACT).exists()
    assert (tmp_path / owner.RUN_ROOT / "summary.json").exists()
    assert (tmp_path / owner.RUN_ROOT / "raw_metrics.jsonl").exists()
    assert (tmp_path / owner.RUN_ROOT / "claim_capsule.json").exists()
    assert (tmp_path / owner.RUN_ROOT / "report.md").exists()
