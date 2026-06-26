import json
import sys
import types
from pathlib import Path

import pytest

from bedc_quality_lab import metric_purity


CASES = [
    ("information_starved_baseline", "CV-HG1"),
    ("unanswerable_ood", "CV-HG2"),
    ("arm_identity_metric_injection", "CV-HG5"),
    ("hand_gate_advantage", "CV-HG4"),
    ("table_coverage_saturation", "CV-HG3"),
]


def _fake_construct_validity_module():
    def _failed_gate(payload):
        if payload.get("task_variables") is None:
            return "CV-HG1"
        if payload.get("arm_input_access", {}).get("label_invisibility_certificate") is False:
            return "CV-HG2"
        if payload.get("finite_table", {}).get("table_coverage_only") is True:
            return "CV-HG3"
        if payload.get("hand_feature_ledger", {}).get("candidate_only_features"):
            return "CV-HG4"
        if payload.get("metric_source", {}).get("per_arm_constants") is True:
            return "CV-HG5"
        return "CV-HG1"

    def evaluate_construct_validity(payload):
        failed_gate = _failed_gate(payload)
        return {
            "status": "fail",
            "failed_gates": [failed_gate],
            "gates": {failed_gate: {"status": "fail"}},
        }

    return types.SimpleNamespace(evaluate_construct_validity=evaluate_construct_validity)


def _write_single_pathology_config(tmp_path, fixture_id, reason):
    artifact = f"tests/fixtures/metric_purity/pathology/{fixture_id}.json"
    target = {
        "id": f"pathology-{fixture_id}",
        "kind": "pathology",
        "module": "bedc_quality_lab.construct_validity",
        "callable": "evaluate_construct_validity",
        "owner_pointer": "bedc_quality_lab.construct_validity:evaluate_construct_validity",
        "report_artifact": artifact,
        "evidence_pointer": reason,
        "empirical_metric_keys": [],
        "mutation_contract_refs": [reason],
        "allowlist_refs": [],
    }
    targets_path = tmp_path / "targets.json"
    allowlist_path = tmp_path / "allowlist.json"
    targets_path.write_text(
        json.dumps({"schema_id": metric_purity.TARGETS_SCHEMA_ID, "targets": [target], "hardgate_mutations": []}) + "\n",
        encoding="utf-8",
    )
    allowlist_path.write_text(json.dumps({"schema_id": metric_purity.ALLOWLIST_SCHEMA_ID, "rows": []}) + "\n", encoding="utf-8")
    return targets_path, allowlist_path


@pytest.mark.parametrize("fixture_id,reason", CASES)
def test_pathology_fixture_is_red_through_owner_api(tmp_path, monkeypatch, fixture_id, reason):
    monkeypatch.setitem(sys.modules, "bedc_quality_lab.construct_validity", _fake_construct_validity_module())
    targets_path, allowlist_path = _write_single_pathology_config(tmp_path, fixture_id, reason)

    payload = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)
    result = payload["pathology_results"][0]

    assert payload["status"] == "pass"
    assert result["status"] == "pass"
    assert result["owner_status"] == "fail"
    assert result["failed_surface"] == reason
    assert result["reason_code"] == reason


def test_missing_construct_validity_owner_blocks_pathology_audit(tmp_path):
    targets_path, allowlist_path = _write_single_pathology_config(tmp_path, *CASES[0])
    config = json.loads(targets_path.read_text(encoding="utf-8"))
    config["targets"][0]["module"] = "bedc_quality_lab.missing_construct_validity"
    config["targets"][0]["owner_pointer"] = "bedc_quality_lab.missing_construct_validity:evaluate_construct_validity"
    targets_path.write_text(json.dumps(config) + "\n", encoding="utf-8")
    sys.modules.pop("bedc_quality_lab.construct_validity", None)

    payload = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)

    assert payload["status"] == "fail"
    assert any(finding["code"] == "REG-HG3" for finding in payload["findings"])
