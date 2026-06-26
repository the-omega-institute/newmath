import json

import pytest

from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_rho_dose_response_discovery as runner

NO_HELPER = "Dose discovery report projection is script-private: neither debt-dose nor rho-dose discovery may introduce bedc_quality_lab/dose_discovery_projection.py; package scope owns predicate primitives, not experiment-specific report/claim construction."
METRICS = ("linear_identifiability_r2", "approx_identifiability_proxy", "orthogonality_error", "covariance_deviation", "quality_benefit", "quality_cost", "quality_debt", "quality_q")


def _source(nets=(0.0, 0.3, 0.7)):
    rows = {}
    for index, net in enumerate(nets):
        means = (0.1 + net, 0.05 + net / 2, 0.8 - net / 3, 1.2 - net / 2, max(0.0, net - 0.2), 0.06, 1.0, -1.0 + net)
        rows[f"rho_{index}"] = {"rho": index / 2, "metrics": {name: {"mean": value} for name, value in zip(METRICS, means, strict=True)}}
    points = [{"rho": row["rho"], "mean": row["metrics"]["linear_identifiability_r2"]["mean"]} for row in rows.values()]
    return {"records": [{} for _ in nets], "aggregate": {"by_rho": rows}, "target_metric_points": points, "applicability_boundary": {"admitted_family": "test"}}


def test_source_payload_shape_is_required(tmp_path):
    path = tmp_path / "bad.json"
    path.write_text(json.dumps({"aggregate": {"by_rho": {"rho_0": {"metrics": {}}}}, "target_metric_points": [{"rho": 0.0}]}), encoding="utf-8")
    with pytest.raises(ValueError, match="lacks metric means"):
        runner._load_source_payload(path)
    path.write_text(json.dumps({"aggregate": {"by_rho": {"rho_0": {"metrics": {}}}}}), encoding="utf-8")
    with pytest.raises(ValueError, match="aggregate.by_rho and target_metric_points"):
        runner._load_source_payload(path)


def test_projection_predicates_payload_and_rank_control():
    source = _source()
    baseline, level = runner._rho_rows(source)[:2]
    projection = runner._rho_projection(level, baseline)
    passage, claim = projection["passage"], projection["claim"]
    delta = classifier_surface_delta(passage)
    assert delta and shift_information(passage) == len(delta)
    assert positive_discovery(claim) == (bool(delta) and net_information(claim) > 0.0)
    payload = runner._verdict_payload(source)
    row = payload["per_rho_verdicts"][1]
    assert "report_schema_id" not in json.dumps(payload) and "report_kind" not in json.dumps(payload)
    assert payload["scope_seal"] == runner.SCOPE_SEAL
    assert row["surface_delta_count"] == len(delta)
    assert row["shift_information"] == shift_information(passage)
    assert row["positive_discovery"] == positive_discovery(claim)
    control = runner._matched_random_baseline([0.0, 0.25, 0.5, 0.75], [0.0, 0.2, 0.4, 0.9])
    assert runner._spearman([0.0, 0.5, 1.0], [1.0, 2.0, 3.0]) == pytest.approx(1.0)
    assert runner._kendall_tau([0.0, 0.5, 1.0], [3.0, 2.0, 1.0]) == pytest.approx(-1.0)
    assert control == runner._matched_random_baseline([0.0, 0.25, 0.5, 0.75], [0.0, 0.2, 0.4, 0.9])
    assert runner._monotonicity_conclusion([{"positive_discovery": v > 0, "net_information": v} for v in (0, 0.4, 0.8)], {"spearman": 1.0, "kendall_tau": 1.0}, {"observed_exceeds_quantile95": True})["result"] == "monotonic"


def test_categorical_h0_branch():
    payload = runner._verdict_payload(_source((-0.1, -0.2, 1.0, 0.7)))
    conclusion = payload["monotonicity_conclusion"]
    assert [row["positive_discovery"] for row in payload["per_rho_verdicts"]] == [False, False, True, True]
    assert conclusion["result"] == "categorical"
    assert conclusion["h0_debt_dose_specific"] is True
    assert conclusion["h1_monotonic_dose_response_universal"] is False
    assert conclusion["net_information_nondecreasing"] is False


def test_generated_report_carries_categorical_conclusion(tmp_path):
    original_root = runner.ROOT
    runner.ROOT = tmp_path
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).parent.mkdir(parents=True)
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).write_text(json.dumps(_source((-0.1, -0.2, 1.0, 0.7))), encoding="utf-8")
    try:
        runner.main()
    finally:
        runner.ROOT = original_root
    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    conclusion = payload["monotonicity_conclusion"]
    assert conclusion["result"] == "categorical"
    assert conclusion["h0_debt_dose_specific"] is True
    assert conclusion["h1_monotonic_dose_response_universal"] is False
    assert conclusion["net_information_nondecreasing"] is False
    assert "- Conclusion: `categorical`" in (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")


def test_main_writes_reports_without_helper_module(tmp_path):
    original_root = runner.ROOT
    runner.ROOT = tmp_path
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).parent.mkdir(parents=True)
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).write_text(json.dumps(_source()), encoding="utf-8")
    try:
        runner.main()
    finally:
        runner.ROOT = original_root
    payload_text = (tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8")
    assert "report_schema_id" not in payload_text and "report_kind" not in payload_text
    assert "# Rho-dose discovery projection" in (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert not (tmp_path / "bedc_quality_lab/dose_discovery_projection.py").exists(), NO_HELPER
