import json
from pathlib import Path

import numpy as np

from bedc_quality_lab.tasks import jepa_wm_l1 as admission
from bedc_quality_lab.tasks import jepa_wm_l1_evaluator_calibration as calibration


def _fixture_surface(case_count: int = 128):
    batch = admission.make_rank_cases(case_count=case_count, seed=admission.DEFAULT_SEED)
    encoded = calibration.fixture_encoded_surface(batch)
    raw = admission.evaluate_encoded_rank_cases(batch, encoded)
    return batch, encoded, raw


def test_calibration_reuses_admission_owner_surface_and_constants():
    batch, encoded, raw = _fixture_surface()
    payload = calibration.build_payload(
        generated_at="fixture",
        batch=batch,
        encoded_surface=encoded,
        raw_rank=raw,
        bootstrap_resamples=32,
    )

    assert payload["admission_owner"]["producer"] == "bedc_quality_lab.tasks.jepa_wm_l1"
    assert payload["admission_owner"]["json_artifact"] == admission.JSON_ARTIFACT
    assert payload["config"]["negative_count"] == admission.NEGATIVE_COUNT
    assert payload["config"]["choice_count"] == admission.CHOICE_COUNT
    assert payload["config"]["base_chance_margin"] == admission.BASE_CHANCE_MARGIN
    assert payload["raw_admission"]["score_source"] == "admission.evaluate_encoded_rank_cases"
    assert payload["diagnostic_next_step"]["claim_allowed"] is False
    assert "capability" not in json.dumps(payload["diagnostic_next_step"]).lower()


def test_four_arm_calibration_has_one_gate_shape_for_every_scorer():
    batch, encoded, raw = _fixture_surface()
    payload = calibration.build_payload(
        generated_at="fixture",
        batch=batch,
        encoded_surface=encoded,
        raw_rank=raw,
        bootstrap_resamples=32,
    )

    assert [arm["arm_id"] for arm in payload["calibration_arms"]] == [
        "raw",
        "frozen-probe",
        "oracle",
        "label-shuffle",
    ]
    gate_keys = {tuple(arm["validation_gate"].keys()) for arm in payload["calibration_arms"]}
    assert gate_keys == {
        (
            "status",
            "criterion",
            "margin",
            "base",
            "empirical_chance",
            "chance_selected_baseline",
            "chance_components",
            "ci_margin_delta",
        )
    }
    by_arm = {arm["arm_id"]: arm for arm in payload["calibration_arms"]}
    assert by_arm["frozen-probe"]["scorer"] == "frozen-ridge-probe"
    assert by_arm["frozen-probe"]["input_pointer"] == "$.calibration_inputs.frozen_probe"
    assert by_arm["oracle"]["validation_gate"]["status"] == "pass"
    assert by_arm["label-shuffle"]["validation_gate"]["status"] == "fail"
    assert payload["hardgate"]["status"] == "diagnostic-only"
    assert all(gate["claim_allowed"] is False for gate in payload["hardgate"]["gates"].values())


def test_payload_writes_json_markdown_and_fingerprint(tmp_path):
    payload = calibration.write_artifacts(
        root=tmp_path,
        generated_at="fixture",
        case_count=128,
        bootstrap_resamples=32,
    )

    json_path = tmp_path / calibration.JSON_ARTIFACT
    markdown_path = tmp_path / calibration.MARKDOWN_ARTIFACT
    fingerprint_path = tmp_path / calibration.FINGERPRINT_ARTIFACT

    assert json.loads(json_path.read_text(encoding="utf-8")) == payload
    markdown = markdown_path.read_text(encoding="utf-8")
    assert markdown.startswith("# JEPA-WM-L1 Evaluator Calibration")
    assert "capability claim" in markdown
    fingerprint = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    assert fingerprint["schema_id"] == calibration.FINGERPRINT_SCHEMA_ID
    assert fingerprint["report_name"] == "jepa-wm-l1-evaluator-calibration"
    assert fingerprint["json_artifact"] == calibration.JSON_ARTIFACT
    assert fingerprint["markdown_artifact"] == calibration.MARKDOWN_ARTIFACT
    assert fingerprint["inputs"]["admission_owner"]["json_artifact"] == admission.JSON_ARTIFACT


def test_label_shuffle_is_deterministic_without_sleep_or_process_guards():
    batch, encoded, raw = _fixture_surface()
    first = calibration.evaluate_calibration_arms(
        batch,
        encoded,
        raw,
        seed=admission.DEFAULT_SEED,
        bootstrap_resamples=32,
    )
    second = calibration.evaluate_calibration_arms(
        batch,
        encoded,
        raw,
        seed=admission.DEFAULT_SEED,
        bootstrap_resamples=32,
    )

    assert first == second
    assert Path(calibration.JSON_ARTIFACT).name == "jepa-wm-l1-evaluator-calibration.json"
