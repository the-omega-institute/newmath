import json

import pytest

from bedc_quality_lab.tasks import sti


def test_sti_payload_is_owner_local_accepted_admission():
    payload = sti.build_payload(generated_at="fixture-time")

    assert payload["schema_id"] == sti.SCHEMA_ID
    assert payload["artifact_id"] == sti.ARTIFACT_ID
    assert payload["generated_at"] == "fixture-time"
    assert payload["producer"] == "bedc_quality_lab.tasks.sti"
    assert payload["task_facts"]["owner"] == "bedc_quality_lab.tasks.sti"
    assert payload["task_facts"]["base_margin"] == 0.05
    assert payload["task_facts"]["control_margin"] == 0.02
    assert tuple(payload["task_facts"]["control_ids"]) == sti.CONTROL_IDS
    assert tuple(payload["task_facts"]["control_ids"]) == ("metadata_only", "no_support", "query_only", "shuffled_support")
    assert payload["base_chance_gate"]["criterion"] == "base_acc_L95 > empirical_chance_U95 + base_margin"
    assert payload["base_chance_gate"]["min_margin"] > sti.BASE_MARGIN
    assert payload["controls"]["criterion"] == "max_control_score <= empirical_chance_U95 + control_margin"
    assert payload["verdict"] == "accepted"
    assert payload["hardgate"]["status"] == "pass"
    assert payload["downstream_gate"]["pointer"] == sti.DOWNSTREAM_GATE_POINTER
    sti.validate_sti_payload(payload)


def test_sti_payload_fails_closed_when_a_control_exceeds_margin():
    bad = sti.STIObservation(
        split="bad-control",
        base_acc=0.72,
        base_acc_L95=0.68,
        empirical_chance=0.60,
        empirical_chance_U95=0.62,
        control_scores={
            "metadata_only": 0.65,
            "no_support": 0.59,
            "query_only": 0.60,
            "shuffled_support": 0.58,
        },
    )

    payload = sti.build_payload(generated_at="fixture-time", observations=[bad])

    assert payload["verdict"] == "bounded_negative"
    assert payload["claim_boundary"]["status"] == "bounded-negative"
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["failed_gate"] == "CONTROL"
    assert payload["downstream_gate"]["status"] == "blocked"
    assert payload["controls"]["failed_controls"] == [
        {"split": "bad-control", "control_id": "metadata_only", "delta_over_chance": 0.03}
    ]


def test_sti_payload_fails_closed_when_base_confidence_bound_is_too_close_to_chance():
    bad = sti.STIObservation(
        split="bad-base",
        base_acc=0.70,
        base_acc_L95=0.66,
        empirical_chance=0.60,
        empirical_chance_U95=0.62,
        control_scores={
            "metadata_only": 0.60,
            "no_support": 0.59,
            "query_only": 0.60,
            "shuffled_support": 0.58,
        },
    )

    payload = sti.build_payload(generated_at="fixture-time", observations=[bad])

    assert payload["verdict"] == "bounded_negative"
    assert payload["hardgate"]["failed_gate"] == "BASE-CHANCE"
    assert payload["base_chance_gate"]["min_margin"] == 0.04


def test_sti_validator_rejects_non_owner_control_shape():
    payload = sti.build_payload(generated_at="fixture-time")
    payload["observations"][0]["control_scores"].pop("metadata_only")

    with pytest.raises(ValueError, match="control set mismatch"):
        sti.validate_sti_payload(payload)


def test_sti_write_artifacts_writes_json_markdown_and_fingerprint(tmp_path):
    payload = sti.write_artifacts(root=tmp_path, generated_at="fixture-time")

    json_payload = json.loads((tmp_path / sti.JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / sti.MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    fingerprint = json.loads((tmp_path / sti.FINGERPRINT_ARTIFACT).read_text(encoding="utf-8"))

    assert json_payload == payload
    assert "# STI Admission" in markdown
    assert "base_acc_L95 > empirical_chance_U95 + base_margin" in markdown
    assert "`reports/canonical/sti-admission.json:$.downstream_gate`" in markdown
    assert fingerprint["report_name"] == "sti-admission"
    assert fingerprint["json_artifact"] == sti.JSON_ARTIFACT
