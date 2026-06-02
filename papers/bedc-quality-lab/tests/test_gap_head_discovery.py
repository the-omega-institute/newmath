import copy
import json

import pytest

from bedc_quality_lab.classifier_shift import structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_gap_head_discovery as runner


def _payload():
    return runner._load_gap_head_payload()


def test_load_gap_head_payload_rejects_no_z_leak_failure(tmp_path):
    payload = _payload()
    payload["feature_columns"] = list(payload["feature_columns"]) + ["z"]
    path = tmp_path / "bad.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="forbidden inference column"):
        runner._load_gap_head_payload(path)


def test_load_gap_head_payload_rejects_record_count_mismatch(tmp_path):
    payload = _payload()
    payload["aggregate"]["record_count"] = len(payload["records"]) + 1
    path = tmp_path / "bad.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="record count is incomplete"):
        runner._load_gap_head_payload(path)


def test_projection_has_source_artifacts_and_common_source():
    projection = runner._build_gap_head_projection(_payload())
    verdict = runner._verdict_payload(projection)

    assert verdict["source_artifacts"]["source_json_artifact"] == runner.SOURCE_JSON_ARTIFACT
    assert verdict["source_artifacts"]["producer_script"] == "scripts/run_gap_ledger_head_on_h.py"
    assert verdict["common_source_record_count"] == 30
    assert verdict["surface_delta_count"] == 30
    assert verdict["shift_information"] == 30
    assert verdict["boundary_checks"]["representation_boundary"] == "learned_h"
    assert verdict["boundary_checks"]["inference_no_ground_truth_z"] is True


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
    assert "# Gap-Head Discovery Verdict" in report
    assert "Source JSON artifact" in report
