import copy
import json

import pytest

from bedc_quality_lab.classifier_shift import structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_gap_head_discovery as runner


def _payload():
    payload = runner._load_gap_head_payload()
    _mark_control_audit_verified(payload)
    return payload


def _verified_audit():
    return {
        "parameter_match": True,
        "compute_match": True,
        "threshold_match": True,
        "surface_distribution_match": True,
        "metric_helper_match": True,
        "audit_status": "pass",
        "failure_reasons": [],
        "evidence_pointers": {
            key: [f"fixture:{key}"]
            for key in runner.MATCHED_RANDOM_AUDIT_MATCH_KEYS
        },
    }


def _mark_control_audit_verified(payload):
    payload["control_protocol"] = {
        **payload.get("control_protocol", {}),
        **_verified_audit(),
    }
    for record in payload["records"]:
        record["matched_random_control"] = {
            **record.get("matched_random_control", {}),
            **_verified_audit(),
        }
    return payload


def _write_payload(tmp_path, payload):
    path = tmp_path / "bad.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def test_load_gap_head_payload_rejects_no_z_leak_failure(tmp_path):
    payload = _payload()
    payload["feature_columns"] = list(payload["feature_columns"]) + ["z"]
    path = _write_payload(tmp_path, payload)

    with pytest.raises(ValueError, match="forbidden inference column"):
        runner._load_gap_head_payload(path)


def test_load_gap_head_payload_rejects_record_count_mismatch(tmp_path):
    payload = _payload()
    payload["aggregate"]["record_count"] = len(payload["records"]) + 1
    path = _write_payload(tmp_path, payload)

    with pytest.raises(ValueError, match="record count is incomplete"):
        runner._load_gap_head_payload(path)


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda payload: payload.__setitem__("representation_boundary", "source_h"),
            "learned_h representation boundary",
        ),
        (
            lambda payload: payload.__setitem__("inference_no_ground_truth_z", False),
            "no ground-truth z inference",
        ),
        (
            lambda payload: payload.pop("inference_no_ground_truth_z"),
            "no ground-truth z inference",
        ),
    ],
)
def test_load_gap_head_payload_rejects_top_level_boundary_certificates(tmp_path, mutate, message):
    payload = copy.deepcopy(_payload())
    mutate(payload)
    path = _write_payload(tmp_path, payload)

    with pytest.raises(ValueError, match=message):
        runner._load_gap_head_payload(path)


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda payload: payload["records"][0].__setitem__("representation_boundary", "source_h"),
            "record representation boundary mismatch",
        ),
        (
            lambda payload: payload["records"][0].pop("inference_no_ground_truth_z"),
            "record no-z inference certificate missing",
        ),
        (
            lambda payload: payload["records"][0]["arms"].pop(runner.BEFORE_ARM),
            "before/after arms must share each record",
        ),
        (
            lambda payload: payload["records"][0]["arms"].pop(runner.AFTER_ARM),
            "before/after arms must share each record",
        ),
        (
            lambda payload: payload["records"][1].__setitem__(
                "seed",
                payload["records"][0]["seed"],
            ),
            "common source seed ids must be unique",
        ),
    ],
)
def test_build_gap_head_projection_rejects_record_certificates(mutate, message):
    payload = copy.deepcopy(_payload())
    mutate(payload)

    with pytest.raises(ValueError, match=message):
        runner._build_gap_head_projection(payload)


def test_projection_has_source_artifacts_and_common_source():
    projection = runner._build_gap_head_projection(_payload())
    verdict = runner._verdict_payload(projection)

    assert verdict["source_artifacts"]["source_json_artifact"] == runner.SOURCE_JSON_ARTIFACT
    assert verdict["source_artifacts"]["producer_script"] == "scripts/run_gap_ledger_head_on_h.py"
    assert verdict["scope_seal"] == runner.SCOPE_SEAL
    assert verdict["common_source_record_count"] == 30
    assert verdict["surface_delta_count"] == 30
    assert verdict["shift_information"] == 30
    assert verdict["boundary_checks"]["representation_boundary"] == "learned_h"
    assert verdict["boundary_checks"]["inference_no_ground_truth_z"] is True


def test_custom_source_artifacts_flow_into_projection():
    payload = copy.deepcopy(_payload())
    payload["source_artifacts"]["json_artifact"] = "reports/custom/source-payload.json"
    payload["source_artifacts"]["report_artifact"] = "reports/custom/source-payload.md"
    projection = runner._build_gap_head_projection(payload)
    verdict = runner._verdict_payload(projection)

    cert = projection.passage.target.certificate
    assert cert["source_artifact"] == "reports/custom/source-payload.json"
    assert projection.source_artifacts["source_json_artifact"] == "reports/custom/source-payload.json"
    assert projection.source_artifacts["source_report_artifact"] == "reports/custom/source-payload.md"
    assert verdict["source_artifacts"]["source_json_artifact"] == "reports/custom/source-payload.json"
    assert verdict["source_artifacts"]["source_report_artifact"] == "reports/custom/source-payload.md"
    assert verdict["source_artifacts"]["source_json_artifact"] != runner.SOURCE_JSON_ARTIFACT


def test_positive_branch_matches_existing_predicate():
    projection = runner._build_gap_head_projection(_payload())
    verdict = runner._verdict_payload(projection)

    assert structural_discovery(projection.passage) is True
    assert verdict["structural_discovery"] is True
    assert verdict["positive_discovery"] is True
    assert verdict["net_positive_signal"] == positive_discovery(projection.claim)
    assert verdict["net_positive_signal"] is True
    assert verdict["net_information"] == pytest.approx(net_information(projection.claim))
    assert verdict["non_discovery_reason"] is None
    assert verdict["matched_random_control"]["control_verdict"]["positive"] is False
    assert verdict["main_claim_status"] == "promoted"
    assert verdict["final_main_claim_status"] == "promoted"


def test_control_positive_forces_unresolved_main_claim():
    payload = copy.deepcopy(_payload())
    for record in payload["records"]:
        record["arms"][runner.CONTROL_ARM] = copy.deepcopy(record["arms"][runner.AFTER_ARM])
    payload["aggregate"]["by_arm"][runner.CONTROL_ARM] = copy.deepcopy(
        payload["aggregate"]["by_arm"][runner.AFTER_ARM]
    )
    payload["aggregate"]["comparison"][
        "unlogged_error_rate_delta_matched_random_minus_vanilla"
    ] = copy.deepcopy(payload["aggregate"]["comparison"]["unlogged_error_rate_delta_learned_minus_vanilla"])
    payload["aggregate"]["comparison"][
        "critical_unlogged_error_rate_delta_matched_random_minus_vanilla"
    ] = copy.deepcopy(
        payload["aggregate"]["comparison"]["critical_unlogged_error_rate_delta_learned_minus_vanilla"]
    )
    payload["aggregate"]["comparison"][
        "failure_detection_auroc_delta_matched_random_minus_vanilla"
    ] = copy.deepcopy(
        payload["aggregate"]["comparison"]["failure_detection_auroc_delta_learned_minus_vanilla"]
    )
    payload["control_verdict"] = copy.deepcopy(payload["treatment_verdict"])
    payload["control_verdict"]["arm"] = runner.CONTROL_ARM
    payload["control_verdict"]["positive"] = True

    projection = runner._build_gap_head_projection(payload)
    verdict = runner._verdict_payload(projection)

    assert verdict["positive_discovery"] is True
    assert verdict["matched_random_control"]["control_verdict"]["positive"] is True
    assert verdict["main_claim_status"] == "unresolved"
    assert verdict["main_claim_reason"] == "control_positive"


def test_control_positive_with_missing_audit_forces_unresolved_main_claim():
    payload = copy.deepcopy(_payload())
    payload["control_protocol"].pop("parameter_match")
    payload["control_verdict"]["positive"] = True

    projection = runner._build_gap_head_projection(payload)
    verdict = runner._verdict_payload(projection)

    assert verdict["positive_discovery"] is True
    assert verdict["matched_random_control"]["verified"] is False
    assert verdict["matched_random_control"]["control_verdict"]["positive"] is False
    assert verdict["main_claim_status"] == "unresolved"
    assert verdict["final_main_claim_status"] == "unresolved"
    assert verdict["main_claim_reason"] == "matched_random_control_unverified"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload.__setitem__("control_protocol", "malformed"),
        lambda payload: payload["records"][0]["matched_random_control"].__setitem__(
            "surface_distribution_match",
            False,
        ),
        lambda payload: payload["records"][0]["matched_random_control"].__setitem__(
            "failure_reasons",
            ["fixture_failure"],
        ),
    ],
)
def test_malformed_or_false_control_audit_forces_unresolved_main_claim(mutate):
    payload = copy.deepcopy(_payload())
    mutate(payload)
    payload["control_verdict"]["positive"] = True

    projection = runner._build_gap_head_projection(payload)
    verdict = runner._verdict_payload(projection)

    assert verdict["matched_random_control"]["verified"] is False
    assert verdict["matched_random_control"]["audit_status"] == "fail"
    assert verdict["main_claim_status"] == "unresolved"
    assert verdict["main_claim_reason"] == "matched_random_control_unverified"


def test_control_non_positive_allows_treatment_promotion():
    payload = copy.deepcopy(_payload())
    for record in payload["records"]:
        record["arms"][runner.CONTROL_ARM] = copy.deepcopy(record["arms"][runner.BEFORE_ARM])
    payload["aggregate"]["by_arm"][runner.CONTROL_ARM] = copy.deepcopy(
        payload["aggregate"]["by_arm"][runner.BEFORE_ARM]
    )
    payload["control_verdict"]["positive"] = False

    projection = runner._build_gap_head_projection(payload)
    verdict = runner._verdict_payload(projection)

    assert verdict["positive_discovery"] is True
    assert verdict["matched_random_control"]["control_verdict"]["positive"] is False
    assert verdict["main_claim_status"] == "promoted"
    assert verdict["final_main_claim_status"] == "promoted"


def test_ledger_incomplete_is_non_discovery_reason():
    projection = runner._build_gap_head_projection(_payload(), recorded_rows=frozenset())
    verdict = runner._verdict_payload(projection)

    assert verdict["structural_discovery"] is False
    assert verdict["positive_discovery"] is False
    assert verdict["net_positive_signal"] == positive_discovery(projection.claim)
    assert verdict["non_discovery_reason"] == "ledger_incomplete"


def test_debt_omitted_or_nonpositive_net_blocks_positive_branch():
    omitted = runner._build_gap_head_projection(
        _payload(),
        omitted_debt_terms={"unrecorded_training_search": 2.0},
    )
    omitted_verdict = runner._verdict_payload(omitted)

    assert omitted_verdict["structural_discovery"] is True
    assert omitted_verdict["positive_discovery"] is False
    assert omitted_verdict["non_discovery_reason"] == "debt_omitted"

    nonpositive = runner._build_gap_head_projection(_payload(), debt_scale=100.0)
    nonpositive_verdict = runner._verdict_payload(nonpositive)

    assert nonpositive_verdict["structural_discovery"] is True
    assert nonpositive_verdict["positive_discovery"] is False
    assert nonpositive_verdict["net_information"] <= 0.0
    assert nonpositive_verdict["non_discovery_reason"] == "net_information_nonpositive"


def test_structural_only_branch_reports_protocol_failure():
    projection = runner._build_gap_head_projection(_payload(), laundering_modes=frozenset({"metric_only"}))
    verdict = runner._verdict_payload(projection)

    assert verdict["structural_discovery"] is True
    assert verdict["positive_discovery"] is False
    assert verdict["laundering_modes"] == ["metric_only"]
    assert verdict["non_discovery_reason"] == "laundering_modes_present"


def test_structural_failure_without_ledger_gap_reports_structural_reason():
    payload = copy.deepcopy(_payload())
    for record in payload["records"]:
        record["arms"][runner.AFTER_ARM] = copy.deepcopy(record["arms"][runner.BEFORE_ARM])
        record["arms"][runner.CONTROL_ARM] = copy.deepcopy(record["arms"][runner.BEFORE_ARM])
    projection = runner._build_gap_head_projection(payload)
    verdict = runner._verdict_payload(projection)

    assert verdict["structural_discovery"] is False
    assert verdict["positive_discovery"] is False
    assert verdict["surface_delta_count"] == 0
    assert verdict["non_discovery_reason"] == "structural_discovery_false"


def test_main_writes_report_artifacts(tmp_path):
    source_payload = _payload()
    original_root = runner.ROOT
    runner.ROOT = tmp_path
    reports = tmp_path / "reports"
    reports.mkdir()
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).write_text(
        json.dumps(source_payload),
        encoding="utf-8",
    )

    try:
        runner.main()
        payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
        report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    finally:
        runner.ROOT = original_root

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["source_artifacts"]["source_json_artifact"] == runner.SOURCE_JSON_ARTIFACT
    assert payload["net_positive_signal"] == payload["positive_discovery"]
    assert "matched_random_control" in payload
    assert "main_claim_status" in payload
    assert "# Gap-Head Discovery Verdict" in report
    assert "Source JSON artifact" in report
