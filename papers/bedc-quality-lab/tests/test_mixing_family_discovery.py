import copy

import pytest
from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_mixing_family_discovery as runner


def _payload():
    source = runner._load_source_payload()
    return {"config": copy.deepcopy(source["config"]), "records": copy.deepcopy(source["records"]), "family_aggregates": copy.deepcopy(source["family_aggregates"]), "negative_result_summary": copy.deepcopy(source["negative_result_summary"]), "applicability_boundary": {"claimed_scope": "test"}}


def _rows_by_family(payload):
    return {row["family"]: row for row in payload["verdicts"]}


def _first_target_family(payload):
    baseline = payload["negative_result_summary"]["baseline_family"]
    return next(family for family in payload["config"]["families"] if family != baseline)


def _record_map(payload):
    return {(row["mixing"], int(row["seed"])): row for row in payload["records"]}


def _set_certified(row):
    row["envelope_projection"]["classifier_spec"]["cert_status"] = "certified"


def _set_metric(row, metric, value):
    row["metrics"][metric] = value
    row["envelope_projection"]["metrics"][metric] = value


def _set_debt(row, value):
    row["mixing_debt_item"]["score"] = f"{value:.6f}"


def _set_target_quality_shift(payload, target, *, quality_delta, debt_score):
    baseline = payload["negative_result_summary"]["baseline_family"]
    by_key = _record_map(payload)
    for seed in payload["config"]["seeds"]:
        baseline_row = by_key[(baseline, int(seed))]
        target_row = by_key[(target, int(seed))]
        _set_certified(baseline_row)
        _set_certified(target_row)
        _set_metric(target_row, "quality_q", float(baseline_row["metrics"]["quality_q"]) + quality_delta)
        _set_debt(target_row, debt_score)


def _copy_baseline_metrics_to_target(payload, target):
    baseline = payload["negative_result_summary"]["baseline_family"]
    by_key = _record_map(payload)
    for seed in payload["config"]["seeds"]:
        baseline_row = by_key[(baseline, int(seed))]
        target_row = by_key[(target, int(seed))]
        _set_certified(baseline_row)
        _set_certified(target_row)
        target_row["metrics"] = copy.deepcopy(baseline_row["metrics"])
        target_row["envelope_projection"]["metrics"] = copy.deepcopy(baseline_row["envelope_projection"]["metrics"])


def test_grid_validation_rejects_missing_family_seed_cell():
    payload = _payload()
    payload["records"] = payload["records"][:-1]
    with pytest.raises(ValueError, match="complete family/seed grid"):
        runner._validate_grid(payload)


def test_projection_uses_seed_metric_predicates_and_blockers():
    payload = _payload()
    target = next(f for f in payload["config"]["families"] if f != payload["negative_result_summary"]["baseline_family"])
    projection = runner._project_family(payload, target)
    row, passage, claim = runner._verdict_row(projection), projection["passage"], projection["claim"]
    assert all(source_id.startswith("seed:") and ":metric:" in source_id for source_id in passage.source.source_ids)
    assert row["surface_delta_count"] == len(classifier_surface_delta(passage)) > len(payload["family_aggregates"])
    assert row["shift_information"] == shift_information(passage)
    assert row["structural_discovery"] == structural_discovery(passage)
    assert row["positive_discovery"] == positive_discovery(claim)
    assert row["net_information"] == net_information(claim)
    assert not any("aggregate" in source_id for source_id in row["source_ids"])
    next(r for r in payload["records"] if r["mixing"] == target and int(r["seed"]) == int(payload["config"]["seeds"][0]))["envelope_projection"]["classifier_spec"]["cert_status"] = "not-certified"
    assert any(b["reason"] == "not-certified" for b in runner._verdict_row(runner._project_family(payload, target))["blockers"])


def test_h0_summary_pinned():
    payload = runner._verdict_payload(_payload())
    summary = payload["positive_probe_summary"]
    assert payload["scope_seal"] == runner.SCOPE_SEAL
    assert summary["answer"] == "H0"
    assert summary["second_positive_probe_found"] is False
    assert summary["positive_families"] == []


def test_positive_verdict_branch():
    payload = _payload()
    target = _first_target_family(payload)
    _set_target_quality_shift(payload, target, quality_delta=10.0, debt_score=0.0)
    projection = runner._project_family(payload, target)
    row = runner._verdict_row(projection)
    assert row["family"] == target
    assert row["surface_delta_count"] > 0
    assert row["net_information"] > 0.0
    assert row["positive_discovery"] is True
    assert positive_discovery(projection["claim"]) is True
    assert row["verdict"] == "positive"


def test_negative_verdict_branch():
    payload = _payload()
    target = _first_target_family(payload)
    _set_target_quality_shift(payload, target, quality_delta=-1.0, debt_score=1.0)
    projection = runner._project_family(payload, target)
    row = runner._verdict_row(projection)
    assert row["family"] == target
    assert row["surface_delta_count"] > 0
    assert row["structural_discovery"] is True
    assert structural_discovery(projection["passage"]) is True
    assert row["net_information"] < 0.0
    assert row["positive_discovery"] is False
    assert row["verdict"] == "negative"


def test_h1_summary_when_any_family_positive():
    payload = _payload()
    target = _first_target_family(payload)
    _set_target_quality_shift(payload, target, quality_delta=10.0, debt_score=0.0)
    summary = runner._verdict_payload(payload)["positive_probe_summary"]
    assert summary["answer"] == "H1"
    assert summary["second_positive_probe_found"] is True
    assert target in summary["positive_families"]
    assert summary["positive_families"]


def test_per_family_verdicts_and_blockers_pinned():
    payload = runner._verdict_payload(_payload())
    rows = _rows_by_family(payload)
    expected_families = {"sinusoidal_shear", "parabolic_shear", "realnvp_coupling"}
    expected_reasons = {"not-certified", "net-nonpositive", "predicate-not-positive"}
    assert payload["baseline_family"] == "spiral"
    assert set(rows) == expected_families
    assert len(payload["certification_blockers"]) == 14
    assert {blocker["reason"] for blocker in payload["certification_blockers"]} == expected_reasons
    for family in expected_families:
        row = rows[family]
        reasons = [blocker["reason"] for blocker in row["blockers"]]
        assert row["verdict"] == "not_positive"
        assert len(row["blockers"]) > 0
        assert set(reasons) == expected_reasons
        assert reasons.count("not-certified") > 0
        assert reasons.count("net-nonpositive") == 1
        assert reasons.count("predicate-not-positive") == 1


def test_matched_random_baseline_contract():
    payload = runner._verdict_payload(_payload())
    control = payload["matched_random_baseline"]
    assert control == {
        "seed": 53320260602,
        "permutations": 200,
        "method": "matched-sign-flip-net-information",
        "observed_positive_count": 0,
        "mean_positive_count": 1.57,
        "max_positive_count": 3,
        "quantile95_positive_count": 3,
    }
    assert control == runner._matched_random_baseline(payload["verdicts"])


def test_alternate_verdict_branch():
    payload = _payload()
    target = _first_target_family(payload)
    _copy_baseline_metrics_to_target(payload, target)
    projection = runner._project_family(payload, target)
    row = runner._verdict_row(projection)
    assert row["family"] == target
    assert row["surface_delta_count"] == 0
    assert row["surface_delta"] == []
    assert row["verdict"] == "compression"


def test_empty_surface_delta_blocker_emitted():
    payload = _payload()
    target = _first_target_family(payload)
    _copy_baseline_metrics_to_target(payload, target)
    projection = runner._project_family(payload, target)
    row = runner._verdict_row(projection)
    payload_row = _rows_by_family(runner._verdict_payload(payload))[target]
    assert row["surface_delta_count"] == 0
    assert row["verdict"] != "positive"
    assert any(blocker["reason"] == "empty-surface-delta" for blocker in row["blockers"])
    assert any(blocker["reason"] == "empty-surface-delta" for blocker in payload_row["blockers"])
    assert any(blocker["reason"] == "empty-surface-delta" for blocker in runner._verdict_payload(payload)["certification_blockers"])


def test_payload_fields_control_and_artifact_writes(tmp_path):
    payload = runner._verdict_payload(_payload())
    assert "report_schema_id" not in payload and "report_kind" not in payload
    assert payload["matched_random_baseline"] == runner._matched_random_baseline(payload["verdicts"])
    root = runner.ROOT
    runner.ROOT = tmp_path
    runner._write_payload(payload)
    runner.ROOT = root
    assert (tmp_path / runner.JSON_ARTIFACT).exists()
    assert "# Mixing-family discovery projection" in (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert not (tmp_path / "bedc_quality_lab/mixing_family_discovery.py").exists()
