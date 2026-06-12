from __future__ import annotations

import json

import argparse
import pytest

from bedc_quality_lab.discovery_compiler import capsule
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.toy_latent_planning_bedc import REQUIRED_NOT_CLAIMED
from experiments.toy_latent_planning_bedc import run_toy_latent_planning_bedc as runner


def _record(seed: int, arm: str, success: float, unlogged: float, regret: float) -> dict:
    return {
        "seed": seed,
        "seed_index": 0,
        "arm": arm,
        "lambda_gap": 1.0,
        "safe_planning_success_rate": success,
        "unlogged_error_rate": unlogged,
        "collision_rate": 0.0,
        "unsafe_state_rate": 0.0,
        "mean_planning_regret": regret,
        "prediction_error_mean": 0.1,
        "gap_event_rate": 1.0,
        "source_projection": {"canonical_envelope_run_id": f"fixture-{arm}"},
    }


def _records() -> list[dict]:
    return [
        _record(1, "vanilla_jepa", 0.40, 0.30, 1.20),
        _record(1, "jepa_posthoc_probe", 0.42, 0.20, 1.10),
        _record(1, "jepa_posthoc_bedc_report", 0.45, 0.18, 1.00),
        _record(1, "bedc_jepa_end_to_end", 0.60, 0.10, 0.70),
    ]


def _projection(records: list[dict], tmp_path):
    return runner.build_payload(
        records=records,
        root=tmp_path,
        generated_at="fixture-time",
        config={"lambda_grid": [0.0, 1.0]},
        source_summary={"dependency": "fixture"},
    )


def test_projector_builds_owner_local_claim_capsule_and_g1_boundaries(tmp_path):
    projection = _projection(_records(), tmp_path)
    summary = projection["summary_payload"]
    capsule_payload = projection["claim_capsule_payload"]

    assert capsule_payload["schema_id"] == capsule.CLAIM_CAPSULE_SCHEMA_ID
    assert capsule_payload["capsule_subtype"] == capsule.TOY_LATENT_PLANNING_CLAIM_CAPSULE_SUBTYPE
    assert capsule_payload["source"] == "reports/toy_latent_planning_bedc/summary.json"
    assert summary["g1_hardgates"]["G1-HG2"]["status"] == "pass"
    assert summary["g1_hardgates"]["G1-HG4"]["status"] == "pass"
    assert "action-conditioned transition identification" in capsule_payload["not_claimed"]
    assert capsule_payload["failed_gate"] == "positive-owner-claim-not-promoted"
    assert capsule_payload["u_hardgates"]["status"] == "pass"


def test_owner_arm_not_above_vanilla_fails_g1_hg1_and_capsule(tmp_path):
    records = [
        _record(1, "vanilla_jepa", 0.60, 0.30, 1.20),
        _record(1, "jepa_posthoc_probe", 0.42, 0.20, 1.10),
        _record(1, "jepa_posthoc_bedc_report", 0.45, 0.18, 1.00),
        _record(1, "bedc_jepa_end_to_end", 0.60, 0.10, 0.70),
    ]

    projection = _projection(records, tmp_path)
    summary = projection["summary_payload"]
    capsule_payload = projection["claim_capsule_payload"]

    assert summary["g1_hardgates"]["G1-HG1"]["status"] == "fail"
    assert summary["failed_gate"] == "G1-HG1"
    assert capsule_payload["hardgates"]["G1-HG1"]["status"] == "fail"
    assert capsule_payload["failed_gate"] == "G1-HG1"
    assert capsule_payload["claim_status"] == "failed"


def test_control_arm_beating_owner_fails_g1_hg3_and_capsule(tmp_path):
    records = [
        _record(1, "vanilla_jepa", 0.40, 0.30, 1.20),
        _record(1, "jepa_posthoc_probe", 0.70, 0.20, 1.10),
        _record(1, "jepa_posthoc_bedc_report", 0.45, 0.18, 1.00),
        _record(1, "bedc_jepa_end_to_end", 0.60, 0.10, 0.70),
    ]

    projection = _projection(records, tmp_path)
    summary = projection["summary_payload"]
    capsule_payload = projection["claim_capsule_payload"]
    control_rows = summary["g1_hardgates"]["G1-HG3"]["control_rows"]

    assert summary["g1_hardgates"]["G1-HG3"]["status"] == "fail"
    assert any(row["control_arm"] == "jepa_posthoc_probe" and row["primary_better"] is False for row in control_rows)
    assert summary["failed_gate"] == "G1-HG3"
    assert capsule_payload["hardgates"]["G1-HG3"]["status"] == "fail"
    assert capsule_payload["failed_gate"] == "G1-HG3"
    assert capsule_payload["claim_status"] == "failed"


def test_missing_one_required_control_arm_fails_g1_hg3_and_capsule(tmp_path):
    records = [
        _record(1, "vanilla_jepa", 0.40, 0.30, 1.20),
        _record(1, "jepa_posthoc_probe", 0.42, 0.20, 1.10),
        _record(1, "bedc_jepa_end_to_end", 0.60, 0.10, 0.70),
    ]

    projection = _projection(records, tmp_path)
    summary = projection["summary_payload"]
    capsule_payload = projection["claim_capsule_payload"]
    control_rows = summary["g1_hardgates"]["G1-HG3"]["control_rows"]

    assert summary["g1_hardgates"]["G1-HG3"]["status"] == "fail"
    assert any(
        row["control_arm"] == "jepa_posthoc_bedc_report"
        and row["control_present"] is False
        and row["control_value"] is None
        for row in control_rows
    )
    assert summary["failed_gate"] == "G1-HG3"
    assert capsule_payload["hardgates"]["G1-HG3"]["status"] == "fail"
    assert capsule_payload["failed_gate"] == "G1-HG3"
    assert capsule_payload["claim_status"] == "failed"


def test_missing_all_required_control_arms_fails_g1_hg3_and_capsule(tmp_path):
    records = [
        _record(1, "vanilla_jepa", 0.40, 0.30, 1.20),
        _record(1, "bedc_jepa_end_to_end", 0.60, 0.10, 0.70),
    ]

    projection = _projection(records, tmp_path)
    summary = projection["summary_payload"]
    capsule_payload = projection["claim_capsule_payload"]
    control_rows = summary["g1_hardgates"]["G1-HG3"]["control_rows"]

    assert summary["g1_hardgates"]["G1-HG3"]["status"] == "fail"
    assert {row["control_arm"] for row in control_rows} == {
        "jepa_posthoc_probe",
        "jepa_posthoc_bedc_report",
    }
    assert all(row["control_present"] is False and row["control_value"] is None for row in control_rows)
    assert summary["failed_gate"] == "G1-HG3"
    assert capsule_payload["hardgates"]["G1-HG3"]["status"] == "fail"
    assert capsule_payload["failed_gate"] == "G1-HG3"
    assert capsule_payload["claim_status"] == "failed"


def test_unparseable_required_control_value_fails_g1_hg3_and_capsule(tmp_path):
    records = [
        _record(1, "vanilla_jepa", 0.40, 0.30, 1.20),
        _record(1, "jepa_posthoc_probe", "not-a-number", 0.20, 1.10),
        _record(1, "jepa_posthoc_bedc_report", 0.45, 0.18, 1.00),
        _record(1, "bedc_jepa_end_to_end", 0.60, 0.10, 0.70),
    ]

    projection = _projection(records, tmp_path)
    summary = projection["summary_payload"]
    capsule_payload = projection["claim_capsule_payload"]
    control_rows = summary["g1_hardgates"]["G1-HG3"]["control_rows"]

    assert summary["g1_hardgates"]["G1-HG3"]["status"] == "fail"
    assert any(
        row["control_arm"] == "jepa_posthoc_probe"
        and row["control_present"] is True
        and row["control_value_parseable"] is False
        and row["control_value"] is None
        for row in control_rows
    )
    assert summary["failed_gate"] == "G1-HG3"
    assert capsule_payload["hardgates"]["G1-HG3"]["status"] == "fail"
    assert capsule_payload["failed_gate"] == "G1-HG3"
    assert capsule_payload["claim_status"] == "failed"


def test_action_conditioned_transition_identification_claim_is_blocked(tmp_path):
    projection = runner.build_payload(
        records=_records(),
        root=tmp_path,
        generated_at="fixture-time",
        config={"lambda_grid": [0.0, 1.0]},
    )
    text = json.dumps(projection["summary_payload"], sort_keys=True)

    assert "action-conditioned transition identification" in projection["summary_payload"]["not_claimed"]
    assert "transition identification accepted" not in text


def test_write_artifacts_loader_parity_and_second_write_is_byte_identical(tmp_path):
    projection = runner.build_payload(
        records=_records(),
        root=tmp_path,
        generated_at="fixture-time",
        config={"lambda_grid": [0.0, 1.0]},
    )

    runner.write_artifacts(projection, root=tmp_path)
    paths = [
        tmp_path / "reports/toy_latent_planning_bedc/toy_latent_planning_bedc.json",
        tmp_path / "reports/toy_latent_planning_bedc/claim_capsule.json",
        tmp_path / "reports/toy_latent_planning_bedc/raw_metrics.jsonl",
        tmp_path / "reports/toy_latent_planning_bedc/summary.json",
        tmp_path / "reports/toy_latent_planning_bedc/report.md",
    ]
    first = {path: path.read_bytes() for path in paths}
    runner.write_artifacts(projection, root=tmp_path)
    second = {path: path.read_bytes() for path in paths}
    capsule_payload = json.loads((tmp_path / "reports/toy_latent_planning_bedc/claim_capsule.json").read_text(encoding="utf-8"))

    assert first == second
    assert capsule_payload["u_hardgates"]["status"] == "pass"
    assert set(capsule_payload["not_claimed"]) == set(REQUIRED_NOT_CLAIMED)


def test_thin_owner_runner_can_run_with_monkeypatched_records(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(runner, "collect_records", lambda *, seeds: (_records(), {"dependency": "fixture"}))

    rc = runner.main(["--root", str(tmp_path), "--generated-at", "fixture-time"])

    assert rc == 0
    stdout = json.loads(capsys.readouterr().out)
    assert stdout["run_id"] == "toy_latent_planning_bedc"
    assert (tmp_path / stdout["claim_capsule"]).exists()
    assert (tmp_path / stdout["summary"]).exists()


def test_committed_owner_local_json_pointers_resolve():
    sidecar_path = runner.ROOT / "reports/toy_latent_planning_bedc/toy_latent_planning_bedc.json"
    summary_path = runner.ROOT / "reports/toy_latent_planning_bedc/summary.json"
    capsule_path = runner.ROOT / "reports/toy_latent_planning_bedc/claim_capsule.json"
    sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    capsule_payload = json.loads(capsule_path.read_text(encoding="utf-8"))

    assert resolve_artifact_pointer(runner.ROOT, sidecar["hardgate_status_pointer"]) == "pass"
    assert resolve_artifact_pointer(
        runner.ROOT,
        f"{summary['result']['claim_capsule_ref']['artifact']}:{summary['result']['claim_capsule_ref']['pointer']}",
    ) == capsule_payload
    assert sidecar["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert capsule_payload["claim_status"] == "failed"


def test_owner_runner_rejects_empty_seed_list():
    with pytest.raises(argparse.ArgumentTypeError):
        runner._parse_int_list("")
