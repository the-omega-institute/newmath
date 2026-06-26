import copy
import json

import pytest

from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_dose_response_discovery as runner
def _source(nets=(0.0, 0.2, 0.4)):
    def row(index, net):
        level = index / 10
        return {"debt_level": level, "metrics": {"quality_q": {"mean": 1.0 - net}, "quality_debt": {"mean": level}, "target_score": {"mean": max(0.0, net - 0.1)}, "linear_identifiability_r2": {"mean": 0.99 - level}, "approx_identifiability_proxy": {"mean": 0.95 - level}}}
    return {"aggregate": {"by_level": {f"{index / 10:.1f}": row(index, net) for index, net in enumerate(nets)}, "record_count": len(nets)}, "applicability_boundary": {"claim_scope": "test"}}
def test_source_payload_requires_level_metric_means(tmp_path):
    path = tmp_path / "bad.json"
    path.write_text(json.dumps({"aggregate": {"by_level": {"0.0": {"metrics": {}}}}}), encoding="utf-8")
    with pytest.raises(ValueError, match="lacks metric means"):
        runner._load_source_payload(path)
def test_project_level_reuses_existing_predicates():
    baseline, level = runner._level_rows(runner._load_source_payload())[:2]
    projection = runner._project_level(level, baseline)
    passage, claim = projection["passage"], projection["claim"]
    delta = classifier_surface_delta(passage)
    assert delta and shift_information(passage) == len(delta)
    assert structural_discovery(passage) and positive_discovery(claim)
    assert net_information(claim) > 0.0
def test_positive_requires_surface_delta_and_net_positive_signal():
    baseline, level = runner._level_rows(runner._load_source_payload())[:2]
    zero_projection = runner._project_level(baseline, baseline)
    weak_level = copy.deepcopy(level)
    weak_level["metrics"]["quality_q"]["mean"] = baseline["metrics"]["quality_q"]["mean"]
    weak_level["metrics"]["quality_debt"]["mean"] = weak_level["metrics"]["target_score"]["mean"] = 0.0
    weak_projection = runner._project_level(weak_level, baseline)
    assert not classifier_surface_delta(zero_projection["passage"])
    assert not positive_discovery(zero_projection["claim"])
    assert net_information(weak_projection["claim"]) <= 0.0
    assert not positive_discovery(weak_projection["claim"])
def test_rank_correlation_is_deterministic_and_directional():
    assert runner._spearman([0.0, 0.1, 0.2], [1.0, 2.0, 3.0]) == pytest.approx(1.0)
    assert runner._spearman([0.0, 0.1, 0.2], [3.0, 2.0, 1.0]) == pytest.approx(-1.0)
    assert runner._kendall_tau([0.0, 0.1, 0.2], [1.0, 2.0, 3.0]) == pytest.approx(1.0)
def test_matched_random_control_is_deterministic():
    args = ([0.0, 0.1, 0.2, 0.3], [0.0, 0.1, 0.3, 0.6])
    first = runner._matched_random_baseline(*args)
    assert first == runner._matched_random_baseline(*args)
    assert first["seed"] == runner.CONTROL_SEED
    assert first["permutations"] == runner.CONTROL_PERMUTATIONS
def test_monotonic_and_categorical_branches_are_reported():
    rows = [{"positive_discovery": value > 0.0, "net_information": value} for value in (0.0, 0.3, 0.6)]
    control = {"observed_exceeds_quantile95": True}
    assert runner._monotonicity_conclusion(rows, {"spearman": 1.0, "kendall_tau": 1.0}, control)["result"] == "monotonic"
    assert runner._monotonicity_conclusion(rows, {"spearman": 0.5, "kendall_tau": 0.5}, control)["result"] == "categorical"
def test_verdict_payload_fields_and_predicate_values():
    source = _source()
    payload = runner._verdict_payload(source)
    levels = runner._level_rows(source)
    projection = runner._project_level(levels[1], levels[0])
    row = payload["per_dose_verdicts"][1]
    assert "report_schema_id" not in json.dumps(payload)
    assert "report_kind" not in json.dumps(payload)
    assert payload["scope_seal"] == runner.SCOPE_SEAL
    assert row["surface_delta_count"] == len(classifier_surface_delta(projection["passage"]))
    assert row["shift_information"] == shift_information(projection["passage"])
    assert row["positive_discovery"] == positive_discovery(projection["claim"])
def test_main_writes_reports_without_helper_module(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).parent.mkdir(parents=True)
    (tmp_path / runner.SOURCE_JSON_ARTIFACT).write_text(json.dumps(_source()), encoding="utf-8")
    runner.main()
    payload_text = (tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8")
    assert "report_schema_id" not in payload_text and "report_kind" not in payload_text
    assert "# Dose-response discovery projection" in (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert not (tmp_path / "bedc_quality_lab/dose_discovery_projection.py").exists(), "Dose discovery report projection is script-private: neither debt-dose nor rho-dose discovery may introduce bedc_quality_lab/dose_discovery_projection.py; package scope owns predicate primitives, not experiment-specific report/claim construction."
