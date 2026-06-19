import hashlib
import json
from pathlib import Path
import shutil

import pytest

from bedc_quality_lab.tasks import jepa_wm_l1 as admission
from bedc_quality_lab.tasks import jepa_wm_l1_evaluator_calibration as calibration
from bedc_quality_lab.tasks import jepa_wm_l1_three_arm_freeze as freeze
from scripts import run_jepa_wm_l1_three_arm_freeze as runner


def _copy_inputs(tmp_path):
    root = Path(__file__).resolve().parents[1]
    for artifact in (admission.JSON_ARTIFACT, calibration.JSON_ARTIFACT):
        target = tmp_path / artifact
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / artifact, target)


def test_three_arm_freeze_binds_single_venue_to_admission_and_evaluator_sha(tmp_path):
    _copy_inputs(tmp_path)
    payload = freeze.write_artifacts(root=tmp_path, generated_at="fixture")

    assert payload["schema_id"] == freeze.SCHEMA_ID
    assert payload["decision"]["status"] == "ready_for_prediction"
    assert payload["decision"]["prediction_schema_pointer"] == f"{freeze.JSON_ARTIFACT}:$.prediction_schema"
    assert payload["source_artifacts"]["admission"]["sha256"] == hashlib.sha256(
        (tmp_path / admission.JSON_ARTIFACT).read_bytes()
    ).hexdigest()
    assert payload["source_artifacts"]["evaluator_calibration"]["sha256"] == hashlib.sha256(
        (tmp_path / calibration.JSON_ARTIFACT).read_bytes()
    ).hexdigest()
    assert [arm["arm_id"] for arm in payload["venue"]["arms"]] == list(freeze.THREE_ARM_IDS)
    assert [row["slice_id"] for row in payload["venue"]["ood_labels"]] == list(freeze.OOD_SLICE_IDS)
    assert payload["metrics"]["base_chance"]["probability"] == admission.REQUIRED_CHANCE
    assert payload["hardgate"]["status"] == "pass"
    assert payload["stub_smoke"]["status"] == "pass"
    assert payload["decision"]["venue_sha256"] == freeze.venue_content_sha256(payload)


def test_prediction_schema_and_stub_smoke_are_fail_closed(tmp_path):
    _copy_inputs(tmp_path)
    payload = freeze.write_artifacts(root=tmp_path, generated_at="fixture")
    venue_sha = payload["decision"]["venue_sha256"]
    stub = payload["stub_smoke"]["stub_predictions"][0]

    assert freeze.validate_prediction_stub(stub, venue_sha256=venue_sha)["status"] == "pass"
    assert freeze.validate_prediction_stub({**stub, "venue_sha256": "0" * 64}, venue_sha256=venue_sha)["status"] == "fail"
    broken = dict(stub)
    broken["arm_predictions"] = stub["arm_predictions"][:-1]
    assert "arm_ids" in freeze.validate_prediction_stub(broken, venue_sha256=venue_sha)["errors"]
    missing_key = dict(stub)
    missing_key.pop("prediction_id")
    assert "missing:prediction_id" in freeze.validate_prediction_stub(missing_key, venue_sha256=venue_sha)["errors"]
    direct_ref = dict(stub)
    direct_ref["arm_predictions"] = [
        {**row, "input_schema": f"{admission.JSON_ARTIFACT}:$.rank_eval"}
        if row["arm_id"] == "bedc_jepa"
        else row
        for row in stub["arm_predictions"]
    ]
    direct_errors = freeze.validate_prediction_stub(direct_ref, venue_sha256=venue_sha)["errors"]
    assert any(error.startswith("forbidden_owner_ref:") for error in direct_errors)
    assert "directly at admission or evaluator" in " ".join(payload["prediction_schema"]["fail_closed_rules"])


def test_write_artifacts_emits_markdown_fingerprint_and_stub_eval(tmp_path):
    _copy_inputs(tmp_path)
    payload = freeze.write_artifacts(root=tmp_path, generated_at="fixture")

    written = json.loads((tmp_path / freeze.JSON_ARTIFACT).read_text(encoding="utf-8"))
    assert written == payload
    assert (tmp_path / freeze.MARKDOWN_ARTIFACT).read_text(encoding="utf-8").startswith(
        "# JEPA-WM-L1 Three-Arm Freeze"
    )
    fingerprint = json.loads((tmp_path / freeze.FINGERPRINT_ARTIFACT).read_text(encoding="utf-8"))
    assert fingerprint["report_name"] == "jepa-wm-l1-three-arm-freeze"
    assert fingerprint["inputs"]["source_artifacts"]["admission"]["path"] == admission.JSON_ARTIFACT
    stub_eval = json.loads((tmp_path / freeze.STUB_EVAL_JSON_ARTIFACT).read_text(encoding="utf-8"))
    assert stub_eval["status"] == "pass"
    assert stub_eval["source_sha256"] == payload["decision"]["venue_sha256"]
    assert (tmp_path / freeze.STUB_EVAL_MARKDOWN_ARTIFACT).read_text(encoding="utf-8").startswith(
        "# JEPA-WM-L1 Three-Arm Stub Eval"
    )


def test_three_arm_freeze_is_deterministic(tmp_path):
    _copy_inputs(tmp_path)
    first = freeze.write_artifacts(root=tmp_path, generated_at="fixture")
    second = freeze.write_artifacts(root=tmp_path, generated_at="fixture")

    assert first == second
    assert first["decision"]["venue_sha256"] == second["decision"]["venue_sha256"]
    assert first["decision"]["venue_sha256"] == freeze.venue_content_sha256(first)


def test_three_arm_freeze_rejects_missing_or_wrong_input_owner(tmp_path):
    _copy_inputs(tmp_path)
    bad = json.loads((tmp_path / admission.JSON_ARTIFACT).read_text(encoding="utf-8"))
    bad["schema_id"] = "wrong"
    (tmp_path / admission.JSON_ARTIFACT).write_text(json.dumps(bad), encoding="utf-8")

    with pytest.raises(ValueError, match="schema_id mismatch"):
        freeze.build_payload(root=tmp_path, generated_at="fixture")


def test_three_arm_hardgates_fail_closed_on_missing_frozen_owner_facts(tmp_path):
    _copy_inputs(tmp_path)
    missing_ood = json.loads((tmp_path / admission.JSON_ARTIFACT).read_text(encoding="utf-8"))
    del missing_ood["preregistration"]["negative_protocol"]["goal_shuffle"]
    (tmp_path / admission.JSON_ARTIFACT).write_text(json.dumps(missing_ood), encoding="utf-8")

    payload = freeze.write_artifacts(root=tmp_path, generated_at="fixture")

    assert payload["decision"]["status"] == "blocked"
    assert payload["hardgate"]["gates"]["JWM-L1-THREE-ARM-HG4"]["status"] == "fail"
    assert "JWM-L1-THREE-ARM-HG4" in payload["hardgate"]["failed_gates"]


def test_three_arm_hardgates_require_leakage_sources(tmp_path):
    _copy_inputs(tmp_path)
    missing_control = json.loads((tmp_path / admission.JSON_ARTIFACT).read_text(encoding="utf-8"))
    del missing_control["anti_triviality_controls"]["controls"]["metadata_only"]
    (tmp_path / admission.JSON_ARTIFACT).write_text(json.dumps(missing_control), encoding="utf-8")

    payload = freeze.write_artifacts(root=tmp_path, generated_at="fixture")

    assert payload["decision"]["status"] == "blocked"
    assert payload["hardgate"]["gates"]["JWM-L1-THREE-ARM-HG7"]["status"] == "fail"


def test_stub_eval_fails_on_non_mapping_result(tmp_path):
    _copy_inputs(tmp_path)
    payload = freeze.write_artifacts(root=tmp_path, generated_at="fixture")
    payload["stub_smoke"]["results"] = ["bad"]

    assert freeze.stub_eval_payload(payload)["status"] == "fail"


def test_three_arm_freeze_cli_writes_canonical_artifacts(tmp_path, monkeypatch):
    _copy_inputs(tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    runner.main(["--generated-at", "fixture"])

    payload = json.loads((tmp_path / freeze.JSON_ARTIFACT).read_text(encoding="utf-8"))
    assert payload["decision"]["status"] == "ready_for_prediction"
