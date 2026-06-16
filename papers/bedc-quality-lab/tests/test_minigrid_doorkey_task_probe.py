import json

import numpy as np

from bedc_quality_lab import minigrid_doorkey_task_probe as probe


def test_preregistration_capsule_is_digest_locked_and_names_success_criteria():
    capsule = probe.preregistration_capsule(sample_budget=384)

    assert capsule["schema_id"] == probe.PREREG_SCHEMA_ID
    assert capsule["environment"]["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert capsule["base_chance_gate"]["delta"] == probe.BASE_CHANCE_DELTA
    assert capsule["base_chance_gate"]["ci_method"] == "paired-bootstrap-ci95"
    assert capsule["base_chance_gate"]["required_endpoints"] == ["distinction_accuracy", "planning_success_rate"]
    assert capsule["gap_head_success_criteria"]["forbidden_columns"] == list(probe.FORBIDDEN_GAP_HEAD_COLUMNS)
    assert capsule["drt_success_criteria"]["task_success_non_regression"] is True
    assert len(capsule["preregistration_digest"]) == 64

    without_digest = dict(capsule)
    without_digest.pop("preregistration_digest")
    assert probe.canonical_digest(without_digest) == capsule["preregistration_digest"]


def test_gap_head_feature_audit_rejects_forbidden_columns():
    clean = probe.gap_head_feature_audit(("latent:0", "latent:1", "action:left"))
    contaminated = probe.gap_head_feature_audit(("latent:0", "prediction_error", "gap_label"))

    assert clean["status"] == "pass"
    assert contaminated["status"] == "fail"
    assert contaminated["forbidden_hits"] == ["gap_label", "prediction_error"]


def test_base_gate_failure_returns_abstain_and_skips_downstream(monkeypatch):
    monkeypatch.setattr(probe, "dependency_status", lambda: {"gymnasium": "installed", "minigrid": "installed", "torch": "installed"})
    monkeypatch.setattr(
        probe,
        "collect_training_surface",
        lambda **_: probe.TrainingSurface(
            train={"features": np.zeros((8, 3)), "labels": np.zeros(8, dtype=bool), "gaps": np.zeros(8, dtype=bool)},
            validation={"features": np.zeros((8, 3)), "labels": np.zeros(8, dtype=bool), "gaps": np.zeros(8, dtype=bool)},
            test={"features": np.zeros((8, 3)), "labels": np.zeros(8, dtype=bool), "gaps": np.zeros(8, dtype=bool)},
            heldout={"features": np.zeros((8, 3)), "labels": np.zeros(8, dtype=bool), "gaps": np.zeros(8, dtype=bool)},
            planning_validation=[],
            planning_test=[],
            planning_heldout=[],
            action_count=7,
        ),
    )

    payload = probe.build_payload(generated_at="fixture", sample_budget=64, bootstrap_resamples=16)

    assert payload["execution_status"] == "abstain"
    assert payload["claim_boundary"]["status"] == "bounded-negative"
    assert payload["base_chance_gate"]["status"] == "fail"
    assert payload["arms"]["status"] == "not-run"
    assert payload["arms"]["skip_reason"] == "base-chance-gate-failed"
    assert payload["hardgate"]["gates"]["BASE-CHANCE"]["status"] == "fail"


def test_payload_writes_canonical_json_and_markdown(tmp_path, monkeypatch):
    monkeypatch.setattr(probe, "dependency_status", lambda: {"gymnasium": "missing", "minigrid": "missing", "torch": "missing"})

    json_path = tmp_path / "probe.json"
    markdown_path = tmp_path / "probe.md"
    payload = probe.write_artifacts(json_path=json_path, markdown_path=markdown_path, generated_at="fixture")

    assert json.loads(json_path.read_text(encoding="utf-8")) == payload
    assert markdown_path.read_text(encoding="utf-8").startswith("# MiniGrid DoorKey Task Probe")
    assert payload["execution_status"] == "abstain"
    assert payload["hardgate"]["status"] == "fail"
