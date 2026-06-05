import inspect
import json
from pathlib import Path

from bedc_quality_lab.discovery_compiler.capsule import (
    ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
    require_architecture_claim_capsule,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab import ledger_aware_transformer as lat
from scripts import run_canonical_reports as canonical
from scripts import run_ledger_aware_transformer as runner


def _recursive_keys(value):
    if isinstance(value, dict):
        found = set(value)
        for item in value.values():
            found.update(_recursive_keys(item))
        return found
    if isinstance(value, list):
        found = set()
        for item in value:
            found.update(_recursive_keys(item))
        return found
    return set()


def _artifact_payload(root: Path, artifact: str):
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def test_gap_head_reduces_unlogged_error_against_matched_random_control():
    payload = lat.build_payload(generated_at="fixture-time")

    metrics = payload["aggregate_metrics"]
    assert metrics["uer_learned"] < metrics["uer_matched_random"]
    assert metrics["uer_reduction"] > 0.0
    assert isinstance(metrics["false_alarm_delta"], float)
    assert metrics["only_false_alarm_increase"] is False
    assert metrics["multi_surface_uer_reduction_count"] >= 2
    assert payload["ledger"]["forbidden_inference_columns_used"] is False


def test_payload_records_surface_registry_and_no_suite_class():
    payload = lat.build_payload(generated_at="fixture-time")
    classes = {
        name
        for name, value in inspect.getmembers(lat, inspect.isclass)
        if value.__module__ == lat.__name__
    }

    assert "LedgerAwareTransformerProbeSuite" not in classes
    assert "LedgerAwareTransformerConfig" in classes
    assert "records" in payload
    assert "surface_registry" in payload
    assert "surfaces" not in payload
    assert len(payload["records"]) == len(payload["surface_registry"])
    assert all(row["surface_id"] in payload["surface_registry"] for row in payload["records"])
    assert all(row["role"] == "ood_surface" for row in payload["records"])


def test_canonical_spec_uses_landed_pointer_cells():
    spec = canonical._specs_by_name()["ledger-aware-transformer"]

    assert spec.command == ("python3", "scripts/run_ledger_aware_transformer.py")
    assert spec.scope_pointer == "$.applicability_boundary"
    assert spec.cost_pointer == "$.source_artifacts.cost_protocol"
    assert spec.positive_claim_pointer == "$.positive_claim"
    assert spec.control_pointer == "$.control_protocol"
    assert "records" in spec.required_json_keys
    assert "surface_registry" in spec.required_json_keys
    assert "surfaces" not in spec.required_json_keys
    assert "terminal_verdict" not in spec.required_json_keys


def test_canonical_summary_pointers_and_capsule_source_resolve(tmp_path):
    paths = runner.write_report(root=tmp_path, generated_at="fixture-time")
    payload = json.loads(paths["json"].read_text(encoding="utf-8"))
    capsule = pointer_value(payload, payload["claim_capsule_ref"]["pointer"])
    spec = canonical._specs_by_name()["ledger-aware-transformer"]

    for pointer in (
        spec.scope_pointer,
        spec.cost_pointer,
        spec.not_claimed_pointer,
        spec.positive_claim_pointer,
        spec.control_pointer,
        payload["positive_claim"]["evidence_pointer"],
        payload["positive_claim"]["control_pointer"],
        payload["positive_claim"]["surface_registry_pointer"],
    ):
        assert pointer_value(payload, pointer) is not None

    assert capsule["capsule_subtype"] == ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE
    require_architecture_claim_capsule(capsule)
    source = _artifact_payload(tmp_path, capsule["source"])
    assert pointer_value(source, capsule["source_pointer"]) is not None
    for key in ("candidate_pointer", "evidence_pointer"):
        cell = capsule["model_claim"][key]
        assert pointer_value(_artifact_payload(tmp_path, cell["artifact"]), cell["pointer"]) is not None
    for baseline in capsule["model_claim"]["baselines"]:
        assert pointer_value(_artifact_payload(tmp_path, baseline["artifact"]), baseline["pointer"]) is not None


def test_backend_payload_and_capsule_do_not_emit_terminal_verdict(tmp_path):
    paths = runner.write_report(root=tmp_path, generated_at="fixture-time")
    payload = json.loads(paths["json"].read_text(encoding="utf-8"))
    capsule = pointer_value(payload, payload["claim_capsule_ref"]["pointer"])

    assert "terminal_verdict" not in _recursive_keys(payload)
    assert "terminal_verdict" not in _recursive_keys(capsule)
