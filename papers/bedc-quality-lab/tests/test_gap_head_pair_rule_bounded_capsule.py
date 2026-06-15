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
        runner.GAP_HEAD_DISCOVERY_ARTIFACT: {
            "artifact": runner.GAP_HEAD_DISCOVERY_ARTIFACT,
            "source_artifacts": {
                "source_json_artifact": runner.GAP_HEAD_ON_H_ARTIFACT,
                "producer_script": "scripts/run_gap_ledger_head_on_h.py",
                "projection_script": "scripts/run_gap_head_discovery.py",
            },
            "final_main_claim_status": "promoted",
            "positive_discovery": True,
            "matched_random_control": {"verified": True, "control_verdict": {"positive": False}},
            "boundary_checks": {"common_source_seed_order": [1, 2, 3]},
        },
        runner.OBSERVED_DEBT_TRANSFER_ARTIFACT: {
            "artifact_id": runner.OBSERVED_DEBT_TRANSFER_ARTIFACT_ID,
            "artifact": runner.OBSERVED_DEBT_TRANSFER_ARTIFACT,
            "source_artifacts": {
                "gap_head_surface_owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
                "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            },
            "gap_head_on_h_observed_debt_transfer": {
                "status": "pass",
                "discovery_map_pointer": "$.gap_head_on_h_observed_debt_transfer.status",
            },
            "hardgate_evidence": {"HG-A5": {"status": "pass"}},
        },
        runner.ATTRIBUTION_CAPSULE_ARTIFACT: {
            "schema_id": "bedc.quality.claim_capsule",
            "artifact_id": runner.ATTRIBUTION_CAPSULE_ARTIFACT_ID,
            "source_artifacts": {
                "run_artifacts": {"claim_capsule": "reports/runs/a1-canonical/claim_capsule.json"},
                "cost_protocol": {"status": "recorded"},
            },
            "d5_m": {"status": "pass", "passed": True, "failed_gate": None},
            "mechanism_case": {"status": "resolved"},
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
    assert "gap_head_surface.py" not in json.dumps(payload)
    assert "fair_control.py" not in json.dumps(payload)


def test_missing_prerequisite_is_blocked_not_recomputed(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads.pop(runner.OBSERVED_DEBT_TRANSFER_ARTIFACT)
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    observed = payload["prerequisite_checks_by_id"]["gap_head_observed_debt_transfer"]
    assert observed["status"] == "blocked"
    assert observed["reason"] == "missing_artifact"
    assert payload["capsule_verdict"]["status"] == "blocked"
    assert payload["positive_claim"]["status"] == "blocked"
    assert payload["bounded_negative"]["status"] == "not-applicable"


def test_mismatched_prerequisite_pointer_blocks_capsule(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads[runner.GAP_HEAD_DISCOVERY_ARTIFACT]["source_artifacts"]["source_json_artifact"] = (
        "reports/canonical/other.json"
    )
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    discovery = payload["prerequisite_checks_by_id"]["gap_head_discovery"]
    assert discovery["status"] == "blocked"
    assert discovery["reason"] == "mismatched_expected_pointer"
    assert payload["capsule_verdict"]["status"] == "blocked"


def test_mismatched_prerequisite_artifact_id_blocks_capsule(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads[runner.OBSERVED_DEBT_TRANSFER_ARTIFACT]["artifact_id"] = (
        "bedc-quality-lab:other-observed-debt-transfer"
    )
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    observed = payload["prerequisite_checks_by_id"]["gap_head_observed_debt_transfer"]
    assert observed["status"] == "blocked"
    assert observed["reason"] == "mismatched_artifact_id"
    assert observed["expected_artifact_id"] == runner.OBSERVED_DEBT_TRANSFER_ARTIFACT_ID
    assert observed["observed_artifact_id"] == "bedc-quality-lab:other-observed-debt-transfer"
    assert observed["observed_value"] == "pass"
    assert payload["capsule_verdict"]["status"] == "blocked"


def test_unresolved_prerequisite_status_pointer_blocks_capsule(tmp_path, monkeypatch):
    payloads = _source_payloads()
    del payloads[runner.OBSERVED_DEBT_TRANSFER_ARTIFACT]["gap_head_on_h_observed_debt_transfer"][
        "status"
    ]
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    observed = payload["prerequisite_checks_by_id"]["gap_head_observed_debt_transfer"]
    assert observed["status"] == "blocked"
    assert observed["reason"] == "unresolved_status_pointer"
    assert observed["observed_value"] is None
    assert payload["capsule_verdict"]["status"] == "blocked"


def test_non_pass_prerequisite_yields_bounded_negative(tmp_path, monkeypatch):
    payloads = _source_payloads()
    payloads[runner.ATTRIBUTION_CAPSULE_ARTIFACT]["d5_m"] = {
        "status": "blocked",
        "passed": False,
        "failed_gate": "A1-HG3",
    }
    _write_source_payloads(tmp_path, payloads)
    monkeypatch.setattr(runner, "ROOT", tmp_path)

    payload = runner.build_payload(generated_at="fixture-time")

    attribution = payload["prerequisite_checks_by_id"]["gap_head_attribution_capsule"]
    assert attribution["status"] == "bounded-negative"
    assert attribution["observed_value"] == "blocked"
    assert payload["capsule_verdict"]["status"] == "bounded-negative"
    assert payload["bounded_negative"]["status"] == "bounded-negative"
    assert payload["positive_claim"]["status"] == "blocked"


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
