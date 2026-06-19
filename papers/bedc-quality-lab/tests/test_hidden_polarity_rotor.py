import json
import subprocess
import sys

import pytest

from bedc_quality_lab.tasks import hidden_polarity_rotor as hpr


def positive_measured_result():
    return {
        "run_id": "fixture-positive",
        "source": "tests/fixtures/hpr-positive.json",
        "dependency_status": {"status": "available", "backend": "fixture-json"},
        "effect": {
            "score": 0.84,
            "lower_ci": 0.78,
            "chance_upper_ci": 0.55,
            "sample_count": 128,
        },
        "controls": {
            "phase_shuffle": {"score": 0.54, "upper_ci": 0.56, "sample_count": 128},
            "polarity_swap": {"score": 0.53, "upper_ci": 0.55, "sample_count": 128},
            "rotor_blind": {"score": 0.52, "upper_ci": 0.54, "sample_count": 128},
        },
    }


def test_hpr_default_payload_is_diagnostic_only_owner_local_packet():
    payload = hpr.build_payload(generated_at="fixture-time")

    assert payload["schema_id"] == hpr.SCHEMA_ID
    assert payload["artifact_id"] == hpr.ARTIFACT_ID
    assert payload["generated_at"] == "fixture-time"
    assert payload["producer"] == "bedc_quality_lab.tasks.hidden_polarity_rotor"
    assert payload["task_facts"]["owner"] == "bedc_quality_lab.tasks.hidden_polarity_rotor"
    assert payload["task_facts"]["control_ids"] == list(hpr.CONTROL_IDS)
    assert tuple(payload["config"]["verdicts"]) == hpr.VERDICTS
    assert payload["verdict"] == "diagnostic_only"
    assert payload["dependency_status"]["status"] == "downgraded"
    assert payload["hardgate"]["status"] == "diagnostic"
    assert payload["claim_boundary"]["claim_kind"] is None
    assert payload["diagnostic_fixture"]["control_arm_ids"] == list(hpr.CONTROL_IDS)
    hpr.validate_hpr_payload(payload)


def test_hpr_positive_measured_result_opens_claim_boundary_only():
    payload = hpr.build_payload(generated_at="fixture-time", measured_result=positive_measured_result())

    assert payload["verdict"] == "positive"
    assert payload["hardgate"]["status"] == "pass"
    assert payload["evidence_gate"]["effect_margin"] == 0.23
    assert payload["controls"]["status"] == "pass"
    assert payload["claim_boundary"]["claim_kind"] == hpr.CLAIM_KIND
    assert "claim_kind" not in payload
    assert "claim_kind" not in payload["task_facts"]
    assert "claim_kind" not in payload["preregistration"]


def test_hpr_bounded_negative_when_evidence_margin_fails():
    measured = positive_measured_result()
    measured["effect"]["lower_ci"] = 0.62

    payload = hpr.build_payload(generated_at="fixture-time", measured_result=measured)

    assert payload["verdict"] == "bounded_negative"
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["failed_gate"] == "IDENTIFIABILITY"
    assert payload["claim_boundary"]["claim_kind"] is None
    assert payload["evidence_gate"]["effect_margin"] == 0.07


def test_hpr_ill_posed_when_control_arms_are_not_authorized():
    measured = positive_measured_result()
    measured["controls"].pop("rotor_blind")

    payload = hpr.build_payload(generated_at="fixture-time", measured_result=measured)

    assert payload["verdict"] == "ill_posed"
    assert payload["dependency_status"]["status"] == "blocked"
    assert payload["hardgate"]["failed_gate"] == "MEASURED-RESULT"
    assert payload["controls"]["failed_controls"] == [{"control_id": "shape", "reason": "measured_result_ill_posed"}]
    assert "control set mismatch" in payload["measured_result_intake"]["shape_errors"]


def test_hpr_bounded_negative_when_control_exceeds_chance_envelope():
    measured = positive_measured_result()
    measured["controls"]["phase_shuffle"]["upper_ci"] = 0.61

    payload = hpr.build_payload(generated_at="fixture-time", measured_result=measured)

    assert payload["verdict"] == "bounded_negative"
    assert payload["hardgate"]["failed_gate"] == "CONTROL"
    assert payload["controls"]["failed_controls"] == [{"control_id": "phase_shuffle", "delta_over_chance": 0.06}]


def test_hpr_validator_rejects_claim_kind_outside_claim_boundary():
    payload = hpr.build_payload(generated_at="fixture-time")
    payload["task_facts"]["claim_kind"] = hpr.CLAIM_KIND

    with pytest.raises(ValueError, match="claim_kind must only appear inside claim_boundary"):
        hpr.validate_hpr_payload(payload)


def test_hpr_write_artifacts_writes_json_markdown_and_fingerprint(tmp_path):
    payload = hpr.write_artifacts(root=tmp_path, generated_at="fixture-time")

    json_payload = json.loads((tmp_path / hpr.JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / hpr.MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    fingerprint = json.loads((tmp_path / hpr.FINGERPRINT_ARTIFACT).read_text(encoding="utf-8"))

    assert json_payload == payload
    assert "# Hidden-Polarity Rotor" in markdown
    assert "Claim kind: `None`" in markdown
    assert fingerprint["report_name"] == "hidden-polarity-rotor"
    assert fingerprint["json_artifact"] == hpr.JSON_ARTIFACT
    assert fingerprint["producer_command"] == ["python3", "scripts/run_hidden_polarity_rotor.py"]


def test_hpr_runner_accepts_measured_result_and_writes_summary(tmp_path):
    measured_path = tmp_path / "measured.json"
    summary_path = tmp_path / "summary.json"
    measured_path.write_text(json.dumps(positive_measured_result()), encoding="utf-8")

    subprocess.run(
        [
            sys.executable,
            "scripts/run_hidden_polarity_rotor.py",
            "--generated-at",
            "fixture-time",
            "--measured-result",
            str(measured_path),
            "--json-summary",
            str(summary_path),
        ],
        check=True,
    )

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    artifact = json.loads(open(hpr.JSON_ARTIFACT, encoding="utf-8").read())
    assert summary["verdict"] == "positive"
    assert summary["hardgate_status"] == "pass"
    assert artifact["verdict"] == "positive"
    subprocess.run(
        [
            sys.executable,
            "scripts/run_hidden_polarity_rotor.py",
            "--generated-at",
            hpr.DEFAULT_GENERATED_AT,
        ],
        check=True,
    )
