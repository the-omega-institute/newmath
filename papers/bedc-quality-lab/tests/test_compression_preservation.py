from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


LAB_ROOT = Path(__file__).resolve().parents[1]
RUNNER_PATH = LAB_ROOT / "experiments" / "compression_preservation" / "run_compression_preservation.py"

pytestmark = pytest.mark.skipif(importlib.util.find_spec("torch") is None, reason="torch is not installed")


def _runner():
    spec = importlib.util.spec_from_file_location("compression_preservation_runner", RUNNER_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def _pointer_fields(value):
    if isinstance(value, dict):
        found = []
        for key, item in value.items():
            if key == "evidence_pointer":
                found.append(item)
            found.extend(_pointer_fields(item))
        return found
    if isinstance(value, list):
        found = []
        for item in value:
            found.extend(_pointer_fields(item))
        return found
    return []


def test_compression_preservation_regen_is_byte_identical(tmp_path):
    runner = _runner()
    first = runner.serialize_artifacts(runner.build_artifacts())
    second = runner.serialize_artifacts(runner.build_artifacts())

    assert {path.name: data for path, data in first.items()} == {path.name: data for path, data in second.items()}
    source = json.loads(first[runner.JSON_ARTIFACT].decode("utf-8"))
    assert source["run"]["device"] == "cpu"

    runner.write_artifacts(root=tmp_path)
    before = {path.name: path.read_bytes() for path in tmp_path.iterdir()}
    runner.write_artifacts(root=tmp_path)
    after = {path.name: path.read_bytes() for path in tmp_path.iterdir()}
    assert before == after


def test_claim_capsule_uses_unversioned_schema_and_resolvable_pointers(tmp_path):
    runner = _runner()
    runner.write_artifacts(root=tmp_path)
    loaded = runner.committed_json_round_trip(root=tmp_path)
    source = loaded["compression_preservation"]
    capsule = loaded["claim_capsule"]

    assert capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert ("." + "v" + "1") not in json.dumps(capsule, sort_keys=True)
    assert capsule["claim_id"] == "compression_preservation"
    assert capsule["source_pointer"] == "$.hardgates.H2-HG3"
    assert runner.pointer_value(source, capsule["source_pointer"]) is not None
    assert loaded["summary"]["claim_status"] == capsule["claim_status"]
    assert loaded["raw_metrics"]

    for pointer in _pointer_fields(capsule["hardgates"]):
        assert pointer.startswith("$.")
        assert runner.pointer_value(capsule, pointer) is not None or runner.pointer_value(source, pointer) is not None


def test_performance_preserved_classifier_lost_records_compression_debt():
    runner = _runner()
    payload = runner.build_artifacts()["compression_preservation"]
    student = payload["arms"]["student_performance_distilled"]

    assert student["task_preserved"] is True
    assert payload["hardgates"]["H2-HG1"]["status"] == "pass"
    assert student["classifier_preserved"] is False
    assert student["classifier_agreement"] < student["classifier_agreement_floor"]
    assert payload["hardgates"]["H2-HG2"]["status"] == "fail"
    assert student["compression_debt"]["status"] == "critical"


def test_replay_drift_fails_closed_on_u_hg2(monkeypatch):
    runner = _runner()
    h2_clean_payload = runner._candidate_payload()
    student = h2_clean_payload["arms"]["student_performance_distilled"]
    student["classifier_preserved"] = True
    student["classifier_agreement"] = student["classifier_agreement_floor"]
    student["gap_head_preserved"] = True
    student["gap_head_agreement"] = student["gap_head_agreement_floor"]
    student["ledger_equivalence"] = True
    h2_clean_payload["claimability"]["quality_preserving_compression_claimable"] = True
    h2_clean_payload["hardgates"] = runner._h2_gates(h2_clean_payload)
    monkeypatch.setattr(runner, "_candidate_payload", lambda: h2_clean_payload)

    payload = runner.build_artifacts(deterministic_replay=False)["compression_preservation"]

    assert payload["hardgates"]["H2-HG1"]["status"] == "pass"
    assert payload["hardgates"]["H2-HG2"]["status"] == "pass"
    assert payload["hardgates"]["H2-HG3"]["status"] == "pass"
    assert payload["hardgates"]["U-HG2"]["status"] == "fail"
    assert payload["reproducibility"]["byte_identical"] is False
    assert payload["claim_status"] == "present-but-fail-closed"
    assert payload["claim_status"] != "claimable"
    assert payload["failed_gate"] == "U-HG2"


def test_quality_preserving_claim_requires_classifier_gap_head_and_ledger_equivalence():
    runner = _runner()
    payload = runner.build_artifacts()["compression_preservation"]
    student = payload["arms"]["student_performance_distilled"]

    assert payload["hardgates"]["H2-HG3"]["status"] == "fail"
    assert payload["claimability"]["quality_preserving_compression_claimable"] is False
    assert student["task_preserved"] is True
    assert any(
        value is False
        for value in (
            student["classifier_preserved"],
            student["gap_head_preserved"],
            student["ledger_equivalence"],
        )
    )

    claimable = runner.with_mutated_cell(payload, "$.claimability.quality_preserving_compression_claimable", True)
    claimable["arms"]["student_performance_distilled"]["classifier_preserved"] = True
    claimable["arms"]["student_performance_distilled"]["gap_head_preserved"] = True
    claimable["arms"]["student_performance_distilled"]["ledger_equivalence"] = True
    h2 = runner._h2_gates(claimable)
    assert h2["H2-HG3"]["status"] == "pass"


def test_fail_closed_requires_failed_gate_learning_revocation_and_forbidden_term_audit():
    runner = _runner()
    artifacts = runner.build_artifacts()
    capsule = artifacts["claim_capsule"]

    assert capsule["status"] == "present-but-fail-closed"
    assert capsule["claim_status"] == "present-but-fail-closed"
    assert capsule["failed_gate"]
    assert "classifier-preservation gap" in capsule["what_was_learned"]
    assert "quality-preservation claim" in capsule["what_was_learned"]
    assert len(capsule["revocation"]["rows"]) == 3
    assert {row["condition"] for row in capsule["revocation"]["rows"]} == {
        "evidence-pointer-failure",
        "fixed-seed-regen-drift",
        "classifier-agreement-regression",
    }
    assert capsule["forbidden_claim_term_audit"]["status"] == "pass"
    assert capsule["forbidden_claim_term_audit"]["hits"] == []
    assert set(capsule["not_claimed"]) >= {
        "global model quality",
        "full LeJEPA reproduction",
        "full TensorNameCert",
        "LLM behavior quality",
        "mechanism closure unless D5-M gate passes",
    }
    assert capsule["hardgates"]["U-HG5"]["status"] == "pass"


def test_public_surface_is_pointer_only_when_projected():
    runner = _runner()
    artifacts = runner.build_artifacts()
    summary = artifacts["summary"]
    report = artifacts["report"]

    assert summary["source"] == runner.RUN_ARTIFACTS["compression_preservation"]
    assert summary["source_pointer"] == "$.hardgates.H2-HG3"
    assert "teacher_performance" not in summary
    assert "student_performance_distilled" not in summary
    assert "classifier_agreement" in report
    assert runner.pointer_value(artifacts["compression_preservation"], summary["source_pointer"]) is not None
