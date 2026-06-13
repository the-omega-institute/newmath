import copy
import json
import pytest
from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.claim_projection import METRIC_NAMES, _project_pair
from bedc_quality_lab.discovery import net_information, positive_discovery
from bedc_quality_lab.research_discovery import assign_discovery_level
from scripts import run_certificate_guided_discovery as runner
from scripts import run_certificate_guided_training as training_runner

VALID_SCOPE_SEAL = {
    "status": "closed",
    "toy": True,
    "bounded": True,
    "theorem": False,
    "real_training": False,
    "production_forbidden": True,
}

def _payload():
    payload = training_runner._payload()
    payload["scope_seal"] = VALID_SCOPE_SEAL
    return payload

def _write_payload(tmp_path, payload):
    path = tmp_path / "payload.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path

def _open_training_gate(payload):
    payload["claim_gate"]["positive_quality_improvement"] = True
    payload["claim_gate"]["quality_q_ci95_low"] = 0.1
    payload["claim_gate"]["paired_ci_status"] = "ok"
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["status"] = "ok"
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["ci95_low"] = 0.1

def _close_training_gate(payload):
    payload["claim_gate"]["positive_quality_improvement"] = False
    payload["claim_gate"]["quality_q_ci95_low"] = 0.0
    payload["claim_gate"]["paired_ci_status"] = "ok"
    payload["claim_gate"]["blockers"] = ["quality-q-ci95-low-nonpositive"]

def _role_records(payload, role):
    return [record for record in payload["records"] if record["role"] == role]

def _copy_metrics_by_role(payload, source_role, target_role):
    sources = {record["seed"]: record for record in _role_records(payload, source_role)}
    for target in _role_records(payload, target_role):
        source = sources[target["seed"]]
        for name in METRIC_NAMES:
            target[name] = source[name]

def _shift_metrics_by_role(payload, source_role, target_role, offset):
    sources = {record["seed"]: record for record in _role_records(payload, source_role)}
    for target in _role_records(payload, target_role):
        source = sources[target["seed"]]
        for name in METRIC_NAMES:
            target[name] = source[name] + offset

def _assert_row_matches_predicates(payload, row):
    projection = _project_pair(payload, row["before_role"], row["after_role"])
    passage = projection["passage"]
    claim = projection["claim"]
    delta = classifier_surface_delta(passage)
    assert (row["surface_delta_count"], row["surface_delta"]) == (len(delta), [list(pair) for pair in sorted(delta)])
    assert (row["shift_information"], row["structural_discovery"]) == (shift_information(passage), structural_discovery(passage))
    assert row["net_information"] == pytest.approx(net_information(claim))
    assert row["positive_discovery"] == positive_discovery(claim)

def test_invalid_projection_source_becomes_skipped_payload(tmp_path):
    payload = copy.deepcopy(_payload())
    payload["records"] = [record for record in payload["records"] if record["role"] != runner.CONTROL_ROLE]
    path = _write_payload(tmp_path, payload)
    report = runner._verdict_payload(runner._load_payload(path))

    assert report["producer_status"] == "skipped"
    assert report["positive_discovery"] is None
    assert report["matched_random_baseline"] is None
    assert report["discovery_level"] == "D0"
    assert report["skip_reason"] == runner.SKIP_REASON

    payload = copy.deepcopy(_payload())
    payload["result"]["ledger_rows_written"] = False
    path = _write_payload(tmp_path, payload)
    report = runner._verdict_payload(runner._load_payload(path))

    assert report["producer_status"] == "skipped"
    assert report["skip_reason"] == "certificate-guided payload must record ledger rows"

def test_loader_rejects_missing_claim_gate_or_paired_ci(tmp_path):
    payload = copy.deepcopy(_payload())
    del payload["claim_gate"]
    path = _write_payload(tmp_path, payload)
    report = runner._verdict_payload(runner._load_payload(path))

    assert report["producer_status"] == "skipped"
    assert report["skip_reason"] == "certificate-guided payload must contain claim_gate"

    payload = copy.deepcopy(_payload())
    del payload["paired_delta_ci"]
    path = _write_payload(tmp_path, payload)
    report = runner._verdict_payload(runner._load_payload(path))

    assert report["producer_status"] == "skipped"
    assert report["skip_reason"] == "certificate-guided payload must contain paired quality_q CI evidence"

def test_loader_rejects_when_shared_cost_protocol_name_not_true(tmp_path):
    payload = copy.deepcopy(_payload())
    payload["result"]["shared_cost_protocol_name"] = False
    path = _write_payload(tmp_path, payload)
    report = runner._verdict_payload(runner._load_payload(path))

    assert report["producer_status"] == "skipped"
    assert report["skip_reason"] == "certificate-guided payload must share a cost protocol"

def test_loader_rejects_when_record_lacks_ledger_rows(tmp_path):
    payload = copy.deepcopy(_payload())
    after = next(record for record in payload["records"] if record["role"] == runner.AFTER_ROLE)
    after["ledger_rows"] = []
    path = _write_payload(tmp_path, payload)
    report = runner._verdict_payload(runner._load_payload(path))

    assert report["producer_status"] == "skipped"
    assert report["skip_reason"] == "record lacks ledger rows: after"

def test_certificate_guided_result_is_negative_when_net_is_negative_and_baseline_is_recorded():
    payload = _payload()
    _close_training_gate(payload)
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 1.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = 0.0
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
    assert report["claim_gate"]["positive_discovery_four_gate"] is False
    assert "training-positive-quality-gate-false" in report["claim_gate"]["blockers"]
    assert report["not_claimed"]
    _assert_row_matches_predicates(payload, row)
    assert (baseline["before_role"], baseline["after_role"], baseline["after_candidate_id"]) == (runner.BEFORE_ROLE, runner.CONTROL_ROLE, "matched-random-debt-control")
    assert baseline["positive_discovery"] is False
    _assert_row_matches_predicates(payload, baseline)

def test_nonpositive_net_information_forces_non_positive_discovery_on_classifier_surface():
    payload = _payload()
    _open_training_gate(payload)
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 1.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = 0.0
    row = runner._verdict_payload(payload)["verdicts"][0]

    assert row["structural_discovery"] is True
    assert row["surface_delta_count"] > 0
    assert row["net_information"] <= 0.0
    assert row["positive_discovery"] is False
    assert row["verdict"] == "negative"

def test_zero_net_with_structural_surface_delta_reports_negative():
    payload = copy.deepcopy(_payload())
    _open_training_gate(payload)
    _copy_metrics_by_role(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE)
    before_by_seed = {record["seed"]: record for record in _role_records(payload, runner.BEFORE_ROLE)}
    for after in _role_records(payload, runner.AFTER_ROLE):
        after["quality_benefit"] = before_by_seed[after["seed"]]["quality_benefit"] + 0.25

    projection = _project_pair(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE)
    delta_count = len(classifier_surface_delta(projection["passage"]))
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 0.01 * delta_count
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = 0.0

    report = runner._verdict_payload(payload)
    row = report["verdicts"][0]
    assert row["surface_delta_count"] > 0
    assert row["structural_discovery"] is True
    assert row["positive_discovery"] is False
    assert row["net_information"] == pytest.approx(0.0)
    assert row["verdict"] == "negative"
    assert report["main_claim_status"] == "observed-negative"
    assert "net-information-nonpositive" in report["claim_gate"]["blockers"]
    _assert_row_matches_predicates(payload, row)

def test_compression_verdict_covers_no_surface_delta_case():
    payload = copy.deepcopy(_payload())
    _open_training_gate(payload)
    _copy_metrics_by_role(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE)
    for key in payload["deltas"]["after_minus_before"]:
        payload["deltas"]["after_minus_before"][key] = 0.0
    report = runner._verdict_payload(payload)
    row = report["verdicts"][0]
    assert (row["surface_delta_count"], row["structural_discovery"]) == (0, False)
    assert row["net_information"] == pytest.approx(0.0)
    assert row["positive_discovery"] is False
    assert row["verdict"] == "compression"
    assert report["main_claim_status"] == "mixed"
    assert "empty-classifier-surface-delta" in report["claim_gate"]["blockers"]

def test_missing_scope_seal_blocks_positive_claim_projection():
    payload = _payload()
    payload.pop("scope_seal")
    _open_training_gate(payload)
    _shift_metrics_by_role(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE, 0.25)
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = -1.0

    report = runner._verdict_payload(payload)

    assert report["verdicts"][0]["positive_discovery"] is False
    assert "scope-seal-false" in report["claim_gate"]["blockers"]
    assert report["main_claim_status"] != "positive"


def test_invalid_scope_seal_blocks_positive_claim_projection():
    payload = _payload()
    payload["scope_seal"] = dict(VALID_SCOPE_SEAL, status="open")
    _open_training_gate(payload)
    _shift_metrics_by_role(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE, 0.25)
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = -1.0

    report = runner._verdict_payload(payload)

    assert report["verdicts"][0]["positive_discovery"] is False
    assert "scope-seal-false" in report["claim_gate"]["blockers"]
    assert report["scope_seal"]["status"] == "open"

def test_predicate_positive_does_not_make_main_claim_positive_without_training_gate():
    payload = copy.deepcopy(_payload())
    _close_training_gate(payload)
    _shift_metrics_by_role(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE, 0.25)
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = -1.0

    projection = _project_pair(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE)
    claim = projection["claim"]
    assert positive_discovery(claim) is True
    assert net_information(claim) > 0.0

    report = runner._verdict_payload(payload)
    row = report["verdicts"][0]
    assert row["positive_discovery"] is True
    assert row["net_information"] > 0.0
    assert row["verdict"] == "positive"
    assert report["main_claim_status"] == "mixed"
    assert "training-positive-quality-gate-false" in report["claim_gate"]["blockers"]
    _assert_row_matches_predicates(payload, row)

def test_tradeoff_training_payload_keeps_discovery_main_claim_non_positive():
    payload = copy.deepcopy(_payload())
    _shift_metrics_by_role(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE, 0.25)
    records = payload["records"]
    for before in _role_records(payload, runner.BEFORE_ROLE):
        before["quality_benefit"] = 2.0
        before["quality_debt"] = 1.0
    for after in _role_records(payload, runner.AFTER_ROLE):
        after["quality_benefit"] = 1.5
        after["quality_debt"] = 0.5
    payload["paired_delta_ci"] = training_runner._paired_delta_ci(records)
    payload["claim_gate"] = training_runner._claim_gate(records, payload["paired_delta_ci"])
    payload["not_claimed"] = training_runner._not_claimed(records, payload["paired_delta_ci"])
    payload["deltas"]["after_minus_before"] = training_runner._mean_delta(records, runner.AFTER_ROLE, runner.BEFORE_ROLE)
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0

    assert payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["ci95_low"] > 0.0
    assert payload["claim_gate"]["audit_improvement_tradeoff"] is True
    assert payload["claim_gate"]["positive_quality_improvement"] is False

    report = runner._verdict_payload(payload)
    assert report["main_claim_status"] != "positive"
    assert report["claim_gate"]["positive_discovery_four_gate"] is False
    assert "training-positive-quality-gate-false" in report["claim_gate"]["blockers"]

def test_five_arm_payload_projects_main_control_pair_and_demotes_tradeoff_to_dn():
    payload = copy.deepcopy(_payload())
    report = runner._verdict_payload(payload)
    row = report["verdicts"][0]
    control = report["matched_random_baseline"]

    assert row["before_role"] == "before"
    assert row["after_role"] == "after"
    assert row["after_candidate_id"] == "certificate-guided-sample-support"
    assert control["before_role"] == "before"
    assert control["after_role"] == "control"
    assert control["after_candidate_id"] == "matched-random-debt-control"
    assert control["positive_discovery"] is False
    assert report["hardgate"]["failed_gate"] == "audit-improvement-tradeoff"
    assert report["failed_gate"] == "audit-improvement-tradeoff"
    assert report["verdict"] == "demoted"
    assert report["discovery_level"] == "DN"
    assert assign_discovery_level(report).discovery_level == "DN"

def test_positive_status_requires_classifier_predicate_net_and_training_gate():
    payload = copy.deepcopy(_payload())
    _open_training_gate(payload)
    _shift_metrics_by_role(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE, 0.25)
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 5.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = -1.0

    projection = _project_pair(payload, runner.BEFORE_ROLE, runner.AFTER_ROLE)
    claim = projection["claim"]
    assert positive_discovery(claim) is True
    assert net_information(claim) > 0.0

    report = runner._verdict_payload(payload)
    row = report["verdicts"][0]
    assert row["positive_discovery"] is True
    assert row["net_information"] > 0.0
    assert row["verdict"] == "positive"
    assert report["main_claim_status"] == "positive"
    assert report["claim_gate"]["positive_discovery_four_gate"] is True
    assert report["claim_gate"]["blockers"] == []
    _assert_row_matches_predicates(payload, row)

def test_stale_positive_certificate_cannot_survive_fresh_non_positive_gate():
    payload = copy.deepcopy(_payload())
    payload["certified_claim"] = {"main_claim_status": "positive", "source_artifact": "fixture"}
    _open_training_gate(payload)
    payload["claim_gate"]["quality_q_ci95_low"] = 0.0
    payload["claim_gate"]["audit_improvement_tradeoff"] = False
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["ci95_low"] = 0.0
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 1.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = 0.0

    report = runner._verdict_payload(payload)

    assert report["main_claim_status"] == "observed-negative"
    assert report["revocation_decision"]["downgraded"] is True
    assert report["revocation_decision"]["old_status"] == "positive"
    assert report["revocation_decision"]["new_status"] == "observed-negative"
    assert report["revocation_decision"]["reason"] == "paired-quality-ci-weakened"
    assert len(report["revocation_ledger"]) == 1
    assert report["revocation_ledger"][0] == report["revocation_decision"]["ledger_row"]
    assert report["revocation_ledger"][0]["timestamp"] == report["generated_at"]

def test_absent_certificate_projects_empty_revocation_ledger():
    report = runner._verdict_payload(copy.deepcopy(_payload()))

    assert report["revocation_decision"]["downgraded"] is False
    assert report["revocation_decision"]["reason"] == "no-certified-claim"
    assert report["revocation_decision"]["ledger_row"] == {}
    assert report["revocation_ledger"] == []

def test_no_classifier_surface_delta_or_false_predicate_blocks_positive_status():
    no_surface = copy.deepcopy(_payload())
    _open_training_gate(no_surface)
    _copy_metrics_by_role(no_surface, runner.BEFORE_ROLE, runner.AFTER_ROLE)
    for key in no_surface["deltas"]["after_minus_before"]:
        no_surface["deltas"]["after_minus_before"][key] = 1.0
    no_surface_report = runner._verdict_payload(no_surface)
    assert no_surface_report["main_claim_status"] == "mixed"
    assert "empty-classifier-surface-delta" in no_surface_report["claim_gate"]["blockers"]

    false_predicate = copy.deepcopy(_payload())
    _open_training_gate(false_predicate)
    false_predicate["deltas"]["after_minus_before"]["benefit_delta"] = 0.0
    false_predicate["deltas"]["after_minus_before"]["cost_delta"] = 1.0
    false_predicate_report = runner._verdict_payload(false_predicate)
    assert false_predicate_report["main_claim_status"] != "positive"
    assert "imported-positive-discovery-false" in false_predicate_report["claim_gate"]["blockers"]

def test_payload_uses_pointer_fields_without_schema_kind_fields():
    report = runner._verdict_payload(_payload())

    assert report["artifact"] == runner.JSON_ARTIFACT
    assert report["report"] == runner.REPORT_ARTIFACT
    assert report["projection_script"] == "scripts/run_certificate_guided_discovery.py"
    assert {"artifact", "source_artifacts", "generated_from", "arms", "verdicts"}.issubset(report)
    assert {"revocation_decision", "revocation_ledger"}.issubset(report)
    assert "report_" + "schema_id" not in report
    assert "report_" + "kind" not in report

def test_discovery_payload_contains_audit_decision_and_audit_ledger():
    report = runner._verdict_payload(_payload())

    assert {"audit_decision", "audit_ledger"}.issubset(report)
    assert report["audit_decision"]["audit_status"] in {"consistent", "divergent", "unverifiable"}
    assert report["audit_ledger"] == [report["audit_decision"]["audit_row"]]
    assert report["audit_ledger"][0]["timestamp"] == report["generated_at"]

def test_discovery_payload_records_zero_overclaim_rate_without_forbidden_terms():
    report = runner._verdict_payload(_payload())
    basis = report["audit_decision"]["overclaim_basis"]

    assert basis["checked_claim_count"] > 0
    assert basis["forbidden_claim_fail_count"] == 0
    assert basis["forbidden_claim_term_hits"] == []
    assert report["audit_decision"]["overclaim_rate"] == 0.0

def test_discovery_payload_records_positive_overclaim_rate_for_forbidden_term():
    payload = _payload()
    payload["claim_gate"]["paired_ci_status"] = "full-lejepa"

    report = runner._verdict_payload(payload)
    basis = report["audit_decision"]["overclaim_basis"]

    assert basis["checked_claim_count"] > 0
    assert basis["forbidden_claim_fail_count"] == 1
    assert basis["forbidden_claim_term_hits"] == ["full-lejepa"]
    assert report["audit_decision"]["overclaim_rate"] > 0.0

def test_discovery_markdown_prints_audit_status(tmp_path, monkeypatch):
    payload = runner._verdict_payload(_payload())
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    runner._write_payload(payload)

    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert f"Audit status: `{payload['audit_decision']['audit_status']}`" in report
    assert f"Audit reason: `{payload['audit_decision']['reason']}`" in report
    assert f"Audit ledger rows: `{len(payload['audit_ledger'])}`" in report

def test_audit_decision_does_not_replace_revocation_decision_or_final_status():
    payload = copy.deepcopy(_payload())
    payload["certified_claim"] = {"main_claim_status": "positive", "source_artifact": "fixture"}
    _open_training_gate(payload)
    payload["claim_gate"]["quality_q_ci95_low"] = 0.0
    payload["claim_gate"]["audit_improvement_tradeoff"] = False
    payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["ci95_low"] = 0.0
    payload["deltas"]["after_minus_before"]["benefit_delta"] = 0.0
    payload["deltas"]["after_minus_before"]["cost_delta"] = 1.0
    payload["deltas"]["after_minus_before"]["debt_delta"] = 0.0

    report = runner._verdict_payload(payload)

    assert report["audit_decision"]["audit_status"] == "unverifiable"
    assert report["revocation_decision"]["downgraded"] is True
    assert report["revocation_decision"]["new_status"] == "observed-negative"
    assert report["main_claim_status"] == "observed-negative"

def test_main_writes_report_artifacts(tmp_path, monkeypatch):
    source_payload = _payload()
    _close_training_gate(source_payload)
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
    assert payload["main_claim_status"] != "positive"
    assert payload["revocation_ledger"] == []
    assert "# Certificate-Guided Discovery Projection" in report
    assert f"Benefit declined by `{float(expected_deltas['benefit_delta']):.6f}`" in report
    assert f"Debt declined by `{float(expected_deltas['debt_delta']):.6f}`" in report
    if float(expected_row["net_information"]) > 0.0:
        assert f"Net information cleared zero: `{float(expected_row['net_information']):.6f}`" in report
        assert "Net information did not clear zero" not in report
    else:
        assert f"Net information did not clear zero: `{float(expected_row['net_information']):.6f}`" in report


def test_load_payload_resolves_raw_metrics_relative_to_runner_root(tmp_path, monkeypatch):
    source_payload = copy.deepcopy(_payload())
    source_payload.pop("records")
    raw_path = tmp_path / "reports/runs/certificate-guided-constraint-training/raw_metrics.jsonl"
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in _payload()["records"]),
        encoding="utf-8",
    )
    source_payload["raw_metrics_artifact"] = "reports/runs/certificate-guided-constraint-training/raw_metrics.jsonl"
    source_payload["source_artifacts"]["raw_metrics_artifact"] = source_payload["raw_metrics_artifact"]
    source_path = tmp_path / "reports/canonical/certificate-guided-training.json"
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_text(json.dumps(source_payload, sort_keys=True) + "\n", encoding="utf-8")
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    loaded = runner._load_payload(source_path)
    report = runner._verdict_payload(loaded)

    assert report.get("producer_status") != "skipped"
    assert report["matched_random_baseline"]["after_role"] == runner.CONTROL_ROLE
