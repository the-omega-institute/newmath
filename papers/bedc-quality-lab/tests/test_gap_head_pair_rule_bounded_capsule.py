import copy
import json
from pathlib import Path

from scripts import run_gap_head_pair_rule_bounded_capsule as runner


def _write_json(root: Path, relative_path: str, payload: dict) -> None:
    path = root / relative_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _source_payloads() -> dict[str, dict]:
    return {
        runner.PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT: {
            "artifact_id": runner.PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT_ID,
            "downstream_admission": {
                "status": "pass",
                "owner_pointer": runner.PAIR_RULE_CONSTRUCT_VALIDITY_STATUS_OWNER_POINTER,
            },
            "claim_capsule": {"status": "pass"},
            "source_artifacts": {
                "selected_l1_evidence": runner.PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
            },
        },
        runner.FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT: {
            "artifact_id": runner.FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT_ID,
            "claim_gate": {
                "status": "pass",
                "owner_pointer": runner.FAIR_ALIGNMENT_CONTROL_STATUS_OWNER_POINTER,
            },
            "rows": [
                {
                    "row_id": "gap-head-pair-rule",
                    "task_id": "dgt_l1_order2_pair_rule",
                    "status": "pass",
                }
            ],
        },
        runner.PAIR_RULE_CLAIM_CAPSULE_ARTIFACT: {
            "schema_id": "bedc.quality.claim_capsule",
            "artifact_id": runner.PAIR_RULE_CLAIM_CAPSULE_ARTIFACT_ID,
            "claim_capsule_ref": {
                "construct_validity": {
                    "base_exceeds_chance": {
                        "task_id": "dgt_l1_order2_pair_rule",
                        "chance": 0.0625,
                        "base_acc_mean": 0.25,
                        "base_acc_ci95_low": 0.125,
                        "margin_min": 0.0,
                        "gate_status": "pass",
                        "evidence_pointer": runner.PAIR_RULE_CONSTRUCT_VALIDITY_STATUS_OWNER_POINTER,
                        "fair_control_id": "base_transformer_l1",
                    }
                }
            },
        },
        runner.PAIR_RULE_ATTRIBUTION_ARTIFACT: {
            "artifact_id": runner.PAIR_RULE_ATTRIBUTION_ARTIFACT_ID,
            "d5_m": {
                "status": "pass",
                "source_surface_owner_pointer": runner.PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
            },
        },
        runner.PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT: {
            "artifact_id": runner.PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT_ID,
            "observed_debt_transfer": {
                "status": "pass",
                "source_surface_owner_pointer": runner.PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
            },
        },
    }


def _write_source_payloads(root: Path, payloads: dict[str, dict] | None = None) -> None:
    for artifact, payload in (payloads or _source_payloads()).items():
        _write_json(root, artifact, payload)


def test_pass_capsule_uses_artifact_qualified_prerequisite_pointers(tmp_path, monkeypatch):
    _write_source_payloads(tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    assert payload["artifact_id"] == runner.ARTIFACT_ID
    assert payload["capsule_verdict"]["status"] == "pass"
    assert payload["positive_claim"]["status"] == "pass"
    assert payload["pair_rule_surface"]["order"] == 2
    assert payload["pair_rule_surface"]["starvation_policy"] == "non-starving"
    assert all(row["status"] == "pass" for row in payload["prerequisite_checks"])
    assert all(row["owner_pointer"].startswith("reports/canonical/") for row in payload["prerequisite_checks"])
    assert payload["pair_rule_surface"]["source_surface"]["owner_pointer"] == (
        runner.PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER
    )
    assert "gap_head_surface.py" not in json.dumps(payload)
    assert "fair_control.py" not in json.dumps(payload)
    assert runner.GAUSSIAN_OU_GAP_HEAD_ARTIFACT not in json.dumps(payload)


def test_missing_prerequisite_is_blocked_not_recomputed(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads.pop(runner.FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT)
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    observed = payload["prerequisite_checks_by_id"]["fair_alignment_control_ledger"]
    assert observed["status"] == "blocked"
    assert observed["reason"] == "missing_artifact"
    assert payload["capsule_verdict"]["status"] == "blocked"
    assert payload["positive_claim"]["status"] == "blocked"
    assert payload["bounded_negative"]["status"] == "not-applicable"


def test_mismatched_prerequisite_pointer_blocks_capsule(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads[runner.PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT]["source_artifacts"][
        "selected_l1_evidence"
    ] = (
        "reports/canonical/other.json"
    )
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    construct_validity = payload["prerequisite_checks_by_id"]["pair_rule_construct_validity"]
    assert construct_validity["status"] == "blocked"
    assert construct_validity["reason"] == "mismatched_expected_pointer"
    assert payload["capsule_verdict"]["status"] == "blocked"


def test_mismatched_prerequisite_artifact_id_blocks_capsule(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads[runner.PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT]["artifact_id"] = (
        "bedc-quality-lab:other-pair-rule-observed-debt-transfer"
    )
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    observed = payload["prerequisite_checks_by_id"]["pair_rule_observed_debt_transfer"]
    assert observed["status"] == "blocked"
    assert observed["reason"] == "mismatched_artifact_id"
    assert observed["expected_artifact_id"] == runner.PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT_ID
    assert observed["observed_artifact_id"] == "bedc-quality-lab:other-pair-rule-observed-debt-transfer"
    assert observed["observed_value"] == "pass"
    assert payload["capsule_verdict"]["status"] == "blocked"


def test_unresolved_prerequisite_status_pointer_blocks_capsule(tmp_path, monkeypatch):
    payloads = _source_payloads()
    del payloads[runner.FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT]["claim_gate"]["status"]
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    observed = payload["prerequisite_checks_by_id"]["fair_alignment_control_ledger"]
    assert observed["status"] == "blocked"
    assert observed["reason"] == "unresolved_status_pointer"
    assert observed["observed_value"] is None
    assert payload["capsule_verdict"]["status"] == "blocked"


def test_non_pass_prerequisite_yields_bounded_negative(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads[runner.PAIR_RULE_ATTRIBUTION_ARTIFACT]["d5_m"] = {
        "status": "blocked",
        "source_surface_owner_pointer": runner.PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
        "failed_gate": "A4-HG3",
    }
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    attribution = payload["prerequisite_checks_by_id"]["pair_rule_attribution"]
    assert attribution["status"] == "bounded-negative"
    assert attribution["observed_value"] == "blocked"
    assert payload["capsule_verdict"]["status"] == "bounded-negative"
    assert payload["bounded_negative"]["status"] == "bounded-negative"
    assert payload["bounded_negative"]["bounded_negative_prerequisite_ids"] == ["pair_rule_attribution"]
    assert payload["positive_claim"]["status"] == "blocked"


def test_repository_default_blocks_when_pair_rule_owner_artifacts_are_absent(monkeypatch):
    monkeypatch.setattr(runner, "ROOT", Path("/tmp/nonexistent-pair-rule-owner-root"))

    payload = runner.build_payload(generated_at="fixture-time")

    assert payload["capsule_verdict"]["status"] == "blocked"
    assert {row["reason"] for row in payload["prerequisite_checks"]} == {"missing_artifact"}
    assert payload["positive_claim"]["status"] == "blocked"
    serialized = json.dumps(payload, sort_keys=True)
    assert runner.GAUSSIAN_OU_GAP_HEAD_ARTIFACT not in serialized


def test_write_payload_is_pointer_only_and_deterministic(tmp_path, monkeypatch):
    _write_source_payloads(tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    payload = runner.build_payload(generated_at="fixture-time")

    runner.write_payload(payload)
    first_json = (tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8")
    first_md = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    runner.write_payload(copy.deepcopy(payload))

    assert (tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8") == first_json
    assert (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8") == first_md
    assert "records" not in first_md
    assert "raw payload" not in first_md.lower()
    assert runner.ARTIFACT_ID in first_md
