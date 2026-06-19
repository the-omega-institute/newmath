from __future__ import annotations

import json

import pytest

from bedc_quality_lab.tasks import jepa_wm_l1_ood_adjudication as ood


def _default_rows():
    return [row.as_dict() for row in ood.default_observations()]


def _base_rows_inside_null_band():
    rows = _default_rows()
    null_high_by_split = {
        row["split_id"]: row["ci_high"]
        for row in rows
        if row["arm_id"] == "null"
    }
    for row in rows:
        if row["arm_id"] == "base":
            null_high = null_high_by_split[row["split_id"]]
            row["top1_accuracy"] = round(null_high - 0.005, 6)
            row["ci_low"] = round(null_high - 0.02, 6)
            row["ci_high"] = round(null_high + 0.015, 6)
            row["mean_rank"] = 4.25
            row["calibration_error"] = 0.17
    return rows


def test_preregistration_card_is_single_source_for_fixed_protocol():
    card = ood.preregistration_card()

    assert card["owner"] == "bedc_quality_lab.tasks.jepa_wm_l1_ood_adjudication"
    assert card["fixed_arms"] == ["null", "base", "larger_base", "oracle_or_teacher"]
    assert card["fixed_ood_splits"] == [
        "heldout-dynamics",
        "goal-remap",
        "temporal-gap",
        "distractor-clutter",
    ]
    assert card["metrics"] == ["top1_accuracy", "mean_rank", "calibration_error"]
    assert card["budget_gates"]["min_total_sample_budget"] == 256
    without_digest = {key: value for key, value in card.items() if key != "card_digest"}
    assert card["card_digest"] == ood.canonical_digest(without_digest)


def test_default_payload_success_projects_owner_local_verdict():
    payload = ood.build_payload(generated_at="fixture")

    ood.validate_payload(payload)
    assert payload["schema_id"] == ood.SCHEMA_ID
    assert payload["artifact_id"] == ood.ARTIFACT_ID
    assert len(payload["observations"]) == len(ood.ARM_IDS) * len(ood.SPLIT_IDS)
    assert payload["hardgate"]["status"] == "pass"
    assert payload["verdict"]["status"] == "success"
    assert payload["claim_boundary"]["claim_allowed"] is True
    assert payload["positive_claim"]["positive_discovery"] is True
    assert "No DGT tiny-sequence control extension." in payload["not_claimed"]


def test_budget_failure_is_not_ready_without_adjudication_upgrade():
    payload = ood.build_payload(generated_at="fixture", sample_budget=128)

    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["failed_gates"] == ["BUDGET"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_mixed_ood_evidence_abstains_when_gates_are_valid():
    rows = _default_rows()
    for row in rows:
        if row["split_id"] == "distractor-clutter" and row["arm_id"] == "base":
            row["top1_accuracy"] = 0.151
            row["ci_low"] = 0.132
            row["ci_high"] = 0.164
            row["mean_rank"] = 4.2
            row["calibration_error"] = 0.16

    payload = ood.build_payload(generated_at="fixture", observations=rows)

    assert payload["hardgate"]["status"] == "pass"
    assert payload["verdict"]["status"] == "abstain"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_all_split_kill_evidence_blocks_positive_claim():
    payload = ood.build_payload(generated_at="fixture", observations=_base_rows_inside_null_band())

    assert payload["hardgate"]["status"] == "pass"
    assert {row["status"] for row in payload["split_adjudications"]} == {"kill_candidate"}
    assert payload["verdict"]["status"] == "kill"
    assert payload["claim_boundary"]["claim_allowed"] is False
    assert payload["positive_claim"]["positive_discovery"] is False


def test_missing_metric_fails_closed():
    rows = _default_rows()
    rows[0].pop("mean_rank")

    payload = ood.build_payload(generated_at="fixture", observations=rows)

    assert payload["hardgate"]["status"] == "fail"
    assert "METRICS" in payload["hardgate"]["failed_gates"]
    assert payload["verdict"]["status"] == "not_ready"


def test_unexpected_arm_fails_closed():
    rows = _default_rows()
    for row in rows:
        if row["split_id"] == "heldout-dynamics" and row["arm_id"] == "larger_base":
            row["arm_id"] = "unregistered_arm"
            break

    payload = ood.build_payload(generated_at="fixture", observations=rows)

    assert payload["hardgate"]["status"] == "fail"
    assert "ARMS" in payload["hardgate"]["failed_gates"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_missing_split_fails_closed():
    rows = _default_rows()
    for row in rows:
        if row["split_id"] == "goal-remap":
            row["split_id"] = "unregistered-split"

    payload = ood.build_payload(generated_at="fixture", observations=rows)

    assert payload["hardgate"]["status"] == "fail"
    assert "SPLITS" in payload["hardgate"]["failed_gates"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_control_failure_fails_closed():
    rows = _default_rows()
    for row in rows:
        if row["split_id"] == "heldout-dynamics" and row["arm_id"] == "oracle_or_teacher":
            row["ci_low"] = 0.3
            break

    payload = ood.build_payload(generated_at="fixture", observations=rows)

    assert payload["hardgate"]["status"] == "fail"
    assert "CONTROLS" in payload["hardgate"]["failed_gates"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_write_artifacts_outputs_json_markdown_and_fingerprint(tmp_path):
    payload = ood.write_artifacts(root=tmp_path, generated_at="fixture")

    json_path = tmp_path / ood.JSON_ARTIFACT
    markdown_path = tmp_path / ood.MARKDOWN_ARTIFACT
    fingerprint_path = tmp_path / ood.FINGERPRINT_ARTIFACT
    assert json_path.exists()
    assert markdown_path.exists()
    assert fingerprint_path.exists()
    persisted_payload = json.loads(json_path.read_text(encoding="utf-8"))
    ood.validate_payload(persisted_payload)
    assert persisted_payload["verdict"]["status"] == payload["verdict"]["status"]
    assert "# JEPA-WM-L1 OOD Adjudication" in markdown_path.read_text(encoding="utf-8")
    fingerprint = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    assert fingerprint["report_name"] == "jepa-wm-l1-ood-adjudication"
    assert fingerprint["json_artifact"] == ood.JSON_ARTIFACT
    assert fingerprint["reproducibility_mode"] == "exact_fixture"


def test_validate_payload_rejects_verdict_domain_drift():
    payload = ood.build_payload(generated_at="fixture")
    payload["verdict"] = {**payload["verdict"], "status": "maybe"}

    with pytest.raises(ValueError, match="verdict domain mismatch"):
        ood.validate_payload(payload)
