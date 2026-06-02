import copy
import json
import pytest
from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_certificate_guided_discovery as runner

def _payload():
    return runner._load_payload()

def _write_payload(tmp_path, payload):
    path = tmp_path / "payload.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path

def _assert_row_matches_predicates(payload, row):
    projection = runner._project_pair(payload, row["before_role"], row["after_role"])
    passage = projection["passage"]
    claim = projection["claim"]
    delta = classifier_surface_delta(passage)
    assert (row["surface_delta_count"], row["surface_delta"]) == (len(delta), [list(pair) for pair in sorted(delta)])
    assert (row["shift_information"], row["structural_discovery"]) == (shift_information(passage), structural_discovery(passage))
    assert row["net_information"] == pytest.approx(net_information(claim))
    assert row["positive_discovery"] == positive_discovery(claim)

def test_load_payload_requires_projection_source_shape(tmp_path):
    payload = copy.deepcopy(_payload())
    payload["records"] = [record for record in payload["records"] if record["role"] != runner.CONTROL_ROLE]
    path = _write_payload(tmp_path, payload)
    with pytest.raises(ValueError, match="before, after, and control"):
        runner._load_payload(path)

    payload = copy.deepcopy(_payload())
    payload["result"]["ledger_rows_written"] = False
    path = _write_payload(tmp_path, payload)
    with pytest.raises(ValueError, match="record ledger rows"):
        runner._load_payload(path)

def test_loader_rejects_when_shared_cost_protocol_name_not_true(tmp_path):
    payload = copy.deepcopy(_payload())
    payload["result"]["shared_cost_protocol_name"] = False
    path = _write_payload(tmp_path, payload)
    with pytest.raises(ValueError, match="certificate-guided payload must share a cost protocol"):
        runner._load_payload(path)

def test_loader_rejects_when_record_lacks_ledger_rows(tmp_path):
    payload = copy.deepcopy(_payload())
    after = next(record for record in payload["records"] if record["role"] == runner.AFTER_ROLE)
    after["ledger_rows"] = []
    path = _write_payload(tmp_path, payload)
    with pytest.raises(ValueError, match="record lacks ledger rows: after"):
        runner._load_payload(path)

def test_certificate_guided_result_is_negative_when_net_is_negative_and_baseline_is_recorded():
    payload = _payload()
    report = runner._verdict_payload(payload)
    row = report["verdicts"][0]
    baseline = report["matched_random_baseline"]
    assert (row["before_role"], row["after_role"], row["structural_discovery"]) == (runner.BEFORE_ROLE, runner.AFTER_ROLE, True)
    assert row["surface_delta_count"] > 0
    assert row["net_information"] < 0.0
    assert (row["positive_discovery"], row["verdict"]) == (False, "negative")
    assert report["surface_delta_count"] == row["surface_delta_count"]
    assert report["net_information"] == row["net_information"]
    assert report["positive_discovery"] is False
    assert report["main_claim_status"] == "observed-negative"
    _assert_row_matches_predicates(payload, row)
    assert (baseline["before_role"], baseline["after_role"], baseline["after_candidate_id"]) == (runner.BEFORE_ROLE, runner.CONTROL_ROLE, "torch-request-control")
    _assert_row_matches_predicates(payload, baseline)

def test_nonpositive_net_information_forces_non_positive_discovery_on_classifier_surface():
    payload = _payload()
    row = runner._verdict_payload(payload)["verdicts"][0]

    assert row["structural_discovery"] is True
    assert row["surface_delta_count"] > 0
    assert row["net_information"] <= 0.0
    assert row["positive_discovery"] is False
    assert row["verdict"] == "negative"

def test_compression_verdict_covers_no_surface_delta_case():
    payload = copy.deepcopy(_payload())
    before = next(record for record in payload["records"] if record["role"] == runner.BEFORE_ROLE)
    after = next(record for record in payload["records"] if record["role"] == runner.AFTER_ROLE)
    for name in runner.METRIC_NAMES:
        after[name] = before[name]
    for key in payload["deltas"]["after_minus_before"]:
        payload["deltas"]["after_minus_before"][key] = 0.0
    row = runner._verdict_payload(payload)["verdicts"][0]
    assert (row["surface_delta_count"], row["structural_discovery"]) == (0, False)
    assert row["net_information"] == pytest.approx(0.0)
    assert row["positive_discovery"] is False
    assert row["verdict"] == "compression"

def test_positive_verdict_when_projected_claim_has_positive_net_information():
    payload = copy.deepcopy(_payload())
    before = next(record for record in payload["records"] if record["role"] == runner.BEFORE_ROLE)
    after = next(record for record in payload["records"] if record["role"] == runner.AFTER_ROLE)
    for name in runner.METRIC_NAMES:
        after[name] = before[name] + 0.25
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = -1.0

    projection = runner._project_pair(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE)
    claim = projection["claim"]
    assert positive_discovery(claim) is True
    assert net_information(claim) > 0.0

    row = runner._verdict_payload(payload)["verdicts"][0]
    assert row["positive_discovery"] is True
    assert row["net_information"] > 0.0
    assert row["verdict"] == "positive"
    _assert_row_matches_predicates(payload, row)

def test_payload_uses_pointer_fields_without_schema_kind_fields():
    report = runner._verdict_payload(_payload())

    assert report["artifact"] == runner.JSON_ARTIFACT
    assert report["report"] == runner.REPORT_ARTIFACT
    assert report["projection_script"] == "scripts/run_certificate_guided_discovery.py"
    assert {"artifact", "source_artifacts", "generated_from", "arms", "verdicts"}.issubset(report)
    assert "report_" + "schema_id" not in report
    assert "report_" + "kind" not in report

def test_main_writes_report_artifacts(tmp_path, monkeypatch):
    source_payload = _payload()
    expected = runner._verdict_payload(source_payload)
    expected_row = expected["verdicts"][0]
    expected_deltas = expected_row["deltas"]
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    (tmp_path / "reports").mkdir()
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).write_text(json.dumps(source_payload), encoding="utf-8")
    runner.main()
    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["matched_random_baseline"]["after_role"] == runner.CONTROL_ROLE
    assert payload["positive_discovery"] is False
    assert payload["net_information"] <= 0.0
    assert payload["main_claim_status"] != "positive"
    assert "# Certificate-Guided Discovery Projection" in report
    assert f"Benefit declined by `{float(expected_deltas['benefit_delta']):.6f}`" in report
    assert f"Debt declined by `{float(expected_deltas['debt_delta']):.6f}`" in report
    assert f"Net information did not clear zero: `{float(expected_row['net_information']):.6f}`" in report
