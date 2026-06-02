import copy
import pytest
from bedc_quality_lab.classifier_shift import classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import net_information, positive_discovery
from scripts import run_mixing_family_discovery as runner
def _payload():
    source = runner._load_source_payload()
    return {"config": copy.deepcopy(source["config"]), "records": copy.deepcopy(source["records"]), "family_aggregates": copy.deepcopy(source["family_aggregates"]), "negative_result_summary": copy.deepcopy(source["negative_result_summary"]), "applicability_boundary": {"claimed_scope": "test"}}
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
