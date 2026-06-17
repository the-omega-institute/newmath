from __future__ import annotations

import copy
import hashlib
import json

import numpy as np
import pytest

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.tasks import jepa_wm_l1 as task
from scripts import run_jepa_wm_l1 as runner


def _passing_observation() -> dict[str, object]:
    return {
        "run_id": "fixture-pass",
        "checkpoint": {
            "provenance": {
                "status": "pretrained",
                "source": "public-vjepa2-vitb",
                "checkpoint_sha256": "a" * 64,
                "weights_loaded": True,
                "random_init": False,
            }
        },
        "clips": [
            {"clip_id": "clip-0001", "frame_count": 16},
            {"clip_id": "clip-0002", "frame_count": 16},
        ],
        "k": 7,
        "chance": {"probability": 1.0 / 8.0, "ci_high": 0.20},
        "arms": {
            "null": {"score": 0.13, "ci_low": 0.10, "ci_high": 0.16, "n": 64},
            "oracle_or_teacher": {"score": 0.84, "ci_low": 0.80, "ci_high": 0.88, "n": 64},
            "base": {"score": 0.31, "ci_low": 0.26, "ci_high": 0.36, "n": 64},
            "larger_base": {"score": 0.33, "ci_low": 0.28, "ci_high": 0.38, "n": 64},
        },
        "controls": {
            "metadata_only": {"status": "clean", "ci_high": 0.15, "leak_detected": False},
            "no_context": {"status": "clean", "ci_high": 0.14, "leak_detected": False},
        },
    }


def _mutated_observation(path: tuple[str, ...], value: object) -> dict[str, object]:
    observation = copy.deepcopy(_passing_observation())
    cursor = observation
    for key in path[:-1]:
        cursor = cursor[key]  # type: ignore[index]
    cursor[path[-1]] = value  # type: ignore[index]
    return observation


def _passing_payload() -> dict[str, object]:
    return task.build_payload(_passing_observation(), generated_at="fixture-time", margin=0.05)


def test_jepa_wm_l1_pass_requires_complete_runtime_contract():
    payload = task.build_payload(
        _passing_observation(),
        generated_at="fixture-time",
        margin=0.05,
    )

    assert payload["decision"]["status"] == "PASS"
    assert payload["decision"]["status_domain"] == ["PASS", "bounded_negative", "unavailable"]
    assert payload["decision"]["failed_gates"] == []
    assert payload["admission_contract"]["k"] == 7
    assert payload["admission_contract"]["chance_probability"] == 1.0 / 8.0
    assert payload["admission_contract"]["required_arms"] == [
        "null",
        "oracle_or_teacher",
        "base",
        "larger_base",
    ]
    assert payload["admission_contract"]["required_controls"] == ["metadata_only", "no_context"]
    assert payload["calibration"]["base_CI_low"] == 0.26
    assert payload["calibration"]["chance_CI_high_plus_margin"] == 0.25
    assert all(row["status"] == "pass" for row in payload["hardgates"].values())
    assert "reports/canonical" not in json.dumps(payload, sort_keys=True)


def test_jepa_wm_l1_strict_margin_blocks_boundary_equality():
    observation = _passing_observation()
    observation["arms"]["base"]["ci_low"] = 0.25  # type: ignore[index]
    payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)

    assert payload["decision"]["status"] == "bounded_negative"
    assert payload["hardgates"]["JWM-L1-HG6"]["status"] == "fail"
    assert "JWM-L1-HG6" in payload["decision"]["failed_gates"]


def test_jepa_wm_l1_unavailable_when_runtime_inputs_are_absent():
    cases = [
        (
            _mutated_observation(("checkpoint", "provenance", "checkpoint_sha256"), "not-a-digest"),
            "JWM-L1-HG1",
        ),
        (_mutated_observation(("clips",), []), "JWM-L1-HG2"),
    ]

    for observation, failed_gate in cases:
        payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)
        assert payload["decision"]["status"] == "unavailable"
        assert payload["hardgates"][failed_gate]["status"] == "fail"
        assert failed_gate in payload["decision"]["failed_gates"]


def test_jepa_wm_l1_completed_non_pass_admissions_are_bounded_negative():
    cases = [
        (_mutated_observation(("k",), 5), "JWM-L1-HG3"),
        (_mutated_observation(("chance", "probability"), 0.20), "JWM-L1-HG4"),
        (_mutated_observation(("arms", "larger_base"), None), "JWM-L1-HG5"),
        (_mutated_observation(("controls", "metadata_only", "status"), "leaky"), "JWM-L1-HG7"),
    ]

    for observation, failed_gate in cases:
        payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)
        assert payload["decision"]["status"] == "bounded_negative"
        assert payload["hardgates"][failed_gate]["status"] == "fail"
        assert failed_gate in payload["decision"]["failed_gates"]


def test_jepa_wm_l1_controls_must_not_exceed_chance_band():
    observation = _passing_observation()
    observation["controls"]["metadata_only"]["ci_high"] = 0.21  # type: ignore[index]
    payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)

    assert payload["decision"]["status"] == "bounded_negative"
    assert payload["hardgates"]["JWM-L1-HG7"]["status"] == "fail"
    assert "metadata_only" in payload["hardgates"]["JWM-L1-HG7"]["detail"]


def test_jepa_wm_l1_control_chance_band_equality_is_clean():
    observation = _passing_observation()
    observation["controls"]["metadata_only"]["ci_high"] = 0.20  # type: ignore[index]
    observation["controls"]["no_context"]["ci_high"] = 0.20  # type: ignore[index]
    payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)

    assert payload["decision"]["status"] == "PASS"
    assert payload["hardgates"]["JWM-L1-HG7"]["status"] == "pass"


def test_jepa_wm_l1_rejects_extra_admission_arm():
    observation = _passing_observation()
    observation["arms"]["teacher_hint"] = {  # type: ignore[index]
        "score": 0.50,
        "ci_low": 0.45,
        "ci_high": 0.55,
        "n": 64,
    }
    payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)

    assert payload["decision"]["status"] == "bounded_negative"
    assert payload["hardgates"]["JWM-L1-HG5"]["status"] == "fail"
    assert "unexpected=teacher_hint" in payload["hardgates"]["JWM-L1-HG5"]["detail"]


def test_jepa_wm_l1_build_payload_rejects_negative_margin():
    with pytest.raises(ValueError, match="margin must be nonnegative"):
        task.build_payload(_passing_observation(), generated_at="fixture-time", margin=-0.01)


def test_jepa_wm_l1_validate_payload_rejects_invalid_status_domain():
    payload = _passing_payload()
    payload["decision"]["status"] = "maybe"  # type: ignore[index]

    with pytest.raises(ValueError, match="status domain violation"):
        task.validate_payload(payload)


def test_jepa_wm_l1_validate_payload_rejects_hardgate_order_mismatch():
    payload = _passing_payload()
    hardgates = payload["hardgates"]  # type: ignore[index]
    payload["hardgates"] = dict(reversed(list(hardgates.items())))  # type: ignore[union-attr]

    with pytest.raises(ValueError, match="hardgate order violation"):
        task.validate_payload(payload)


def test_jepa_wm_l1_validate_payload_rejects_failed_gate_projection_mismatch():
    payload = _passing_payload()
    hardgates = payload["hardgates"]  # type: ignore[index]
    hardgates["JWM-L1-HG6"]["status"] = "fail"  # type: ignore[index]

    with pytest.raises(ValueError, match="failed gate projection mismatch"):
        task.validate_payload(payload)


def test_jepa_wm_l1_validate_payload_rejects_pass_with_failed_gate():
    observation = _mutated_observation(("k",), 5)
    payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)
    payload["decision"]["status"] = "PASS"  # type: ignore[index]

    with pytest.raises(ValueError, match="decision status mismatch"):
        task.validate_payload(payload)


def test_jepa_wm_l1_validate_payload_rejects_non_pass_without_failed_gate():
    payload = _passing_payload()
    payload["decision"]["status"] = "bounded_negative"  # type: ignore[index]

    with pytest.raises(ValueError, match="decision status mismatch"):
        task.validate_payload(payload)


def test_jepa_wm_l1_validate_payload_rejects_unavailable_without_runtime_input_failure():
    observation = _mutated_observation(("k",), 5)
    payload = task.build_payload(observation, generated_at="fixture-time", margin=0.05)
    payload["decision"]["status"] = "unavailable"  # type: ignore[index]

    with pytest.raises(ValueError, match="unavailable status mismatch"):
        task.validate_payload(payload)


def test_jepa_wm_l1_validate_payload_rejects_non_pointer_claim_capsule():
    payload = _passing_payload()
    payload["claim_capsule"]["status"] = "inline"  # type: ignore[index]

    with pytest.raises(ValueError, match="claim capsule must be pointer-only"):
        task.validate_payload(payload)


def test_jepa_wm_l1_writes_run_local_pointer_artifacts(tmp_path):
    payload = task.build_payload(_passing_observation(), generated_at="fixture-time", margin=0.05)
    artifacts = task.write_artifacts(payload, root=tmp_path)

    expected_base = tmp_path / "reports" / "runs" / "jepa-wm-l1" / "fixture-pass"
    assert artifacts["admission"] == expected_base / "admission.json"
    assert artifacts["summary"] == expected_base / "summary.json"
    assert artifacts["claim_capsule"] == expected_base / "claim_capsule.json"
    assert artifacts["report"] == expected_base / "report.md"
    assert artifacts["fingerprint"] == expected_base / "fingerprint.json"
    assert artifacts["fingerprint"].exists()
    assert not (tmp_path / "reports" / "canonical" / "index.json").exists()

    capsule = json.loads(artifacts["claim_capsule"].read_text(encoding="utf-8"))
    capsule_text = json.dumps(capsule, sort_keys=True)
    assert capsule["status"] == "pointer-only"
    assert "ci_low" not in capsule_text
    assert resolve_artifact_pointer(tmp_path, capsule["admission_pointer"]) == "PASS"
    for pointer in capsule["hardgate_pointers"]:
        assert resolve_artifact_pointer(tmp_path, pointer) == "pass"

    fingerprint = json.loads(artifacts["fingerprint"].read_text(encoding="utf-8"))
    assert sorted(fingerprint["artifacts"]) == ["admission", "claim_capsule", "report", "summary"]
    for artifact_id, artifact in fingerprint["artifacts"].items():
        assert artifact["path"] == str(artifacts[artifact_id].relative_to(tmp_path))
        digest = hashlib.sha256(artifacts[artifact_id].read_bytes()).hexdigest()
        assert artifact["sha256"] == digest


def test_jepa_wm_l1_cli_writes_run_local_artifacts(tmp_path, capsys):
    input_path = tmp_path / "observation.json"
    input_path.write_text(json.dumps(_passing_observation()), encoding="utf-8")

    assert runner.main(
        [
            "--root",
            str(tmp_path),
            "--input",
            str(input_path),
            "--generated-at",
            "fixture-time",
            "--margin",
            "0.05",
        ]
    ) == 0
    summary = json.loads(capsys.readouterr().out)

    assert summary["artifact_id"] == task.ARTIFACT_ID
    assert summary["run_id"] == "fixture-pass"
    assert summary["status"] == "PASS"
    assert summary["admission_artifact"] == "reports/runs/jepa-wm-l1/fixture-pass/admission.json"
    assert (tmp_path / summary["admission_artifact"]).exists()


def test_jepa_wm_l1_load_observation_rejects_json_array_input(tmp_path):
    input_path = tmp_path / "observation.json"
    input_path.write_text(json.dumps([_passing_observation()]), encoding="utf-8")

    with pytest.raises(ValueError, match="observation input must be a JSON object"):
        task.load_observation(input_path)


def test_jepa_wm_l1_load_observation_rejects_json_scalar_input(tmp_path):
    input_path = tmp_path / "observation.json"
    input_path.write_text(json.dumps("fixture"), encoding="utf-8")

    with pytest.raises(ValueError, match="observation input must be a JSON object"):
        task.load_observation(input_path)



def _loaded_rank_batch(case_count=128):
    true_indices = np.arange(case_count, dtype=np.int64) % task.CHOICE_COUNT
    return task.RankCaseBatch(
        context_videos=np.zeros((case_count, 1, 1, 1, 1), dtype=np.float32),
        candidate_videos=np.zeros((case_count, task.CHOICE_COUNT, 1, 1, 1, 1), dtype=np.float32),
        true_indices=true_indices,
        metadata=[{"case_id": int(index), "true_index": int(true)} for index, true in enumerate(true_indices)],
    )


def _basis_loaded_encoder(batch, *, context_mode):
    basis = np.eye(task.CHOICE_COUNT, dtype=np.float64)

    def encode(videos):
        count = int(videos.shape[0])
        if count == int(batch.true_indices.shape[0]):
            if context_mode == "aligned":
                return basis[batch.true_indices]
            if context_mode == "constant-zero":
                return np.repeat(basis[[0]], count, axis=0)
        if count == int(batch.true_indices.shape[0]) * task.CHOICE_COUNT:
            return np.tile(basis, (int(batch.true_indices.shape[0]), 1))
        raise AssertionError(f"unexpected fake encoder input shape: {videos.shape}")

    return task.LoadedEncoder(
        checkpoint="fixture/vjepa",
        encode=encode,
        metadata={"checkpoint": "fixture/vjepa", "fixture": context_mode},
    )


def _loaded_payload(monkeypatch, *, context_mode):
    batch = _loaded_rank_batch()
    encoder = _basis_loaded_encoder(batch, context_mode=context_mode)
    attempts = [
        task.WeightAttempt(
            checkpoint=encoder.checkpoint,
            status="loaded",
            reason="fixture encoder loaded",
        )
    ]
    monkeypatch.setattr(task, "make_rank_cases", lambda *_args, **_kwargs: batch)
    monkeypatch.setattr(
        task,
        "try_load_public_encoder",
        lambda *_args, **_kwargs: task.WeightLoadResult(encoder, attempts),
    )
    return task.build_payload(generated_at="fixture", case_count=128, bootstrap_resamples=64)


def test_public_encoder_loader_records_dependency_preflight_failure(monkeypatch):
    monkeypatch.setattr(
        task,
        "dependency_status",
        lambda: {
            "torch": "installed",
            "transformers": "missing",
            "huggingface_hub": "installed",
            "torchvision": "installed",
            "PIL": "missing",
            "numpy": "installed",
        },
    )
    monkeypatch.setattr(
        task,
        "dependency_versions",
        lambda: {
            "python": "fixture",
            "torch": "fixture",
            "transformers": "not-installed",
            "huggingface_hub": "fixture",
            "torchvision": "fixture",
            "PIL": "not-installed",
            "numpy": "fixture",
        },
    )

    result = task.try_load_public_encoder(checkpoints=("first", "second"))

    assert result.encoder is None
    assert len(result.attempts) == 1
    attempt = result.attempts[0]
    assert attempt.checkpoint == "dependency-preflight"
    assert attempt.status == "failed"
    assert attempt.stage == "dependency_check"
    assert attempt.reason == "missing dependencies: transformers, PIL"
    assert attempt.details == {
        "dependency_status": {
            "torch": "installed",
            "transformers": "missing",
            "huggingface_hub": "installed",
            "torchvision": "installed",
            "PIL": "missing",
            "numpy": "installed",
        },
        "dependency_versions": {
            "python": "fixture",
            "torch": "fixture",
            "transformers": "not-installed",
            "huggingface_hub": "fixture",
            "torchvision": "fixture",
            "PIL": "not-installed",
            "numpy": "fixture",
        },
    }


def test_public_encoder_loader_aggregates_attempts_and_stops_at_first_success(monkeypatch):
    calls = []
    loaded = task.LoadedEncoder(
        checkpoint="second",
        encode=lambda videos: np.zeros((int(videos.shape[0]), 1), dtype=np.float64),
        metadata={"checkpoint": "second"},
    )

    def fake_load(checkpoint, *, device):
        calls.append((checkpoint, device))
        if checkpoint == "first":
            return task.WeightLoadResult(
                None,
                (
                    task.WeightAttempt(
                        checkpoint="first",
                        status="failed",
                        stage="from_pretrained",
                        reason="fixture miss",
                    ),
                ),
            )
        if checkpoint == "second":
            return task.WeightLoadResult(
                loaded,
                (
                    task.WeightAttempt(
                        checkpoint="second",
                        status="contacted",
                        stage="config",
                        reason="fixture config",
                    ),
                    task.WeightAttempt(
                        checkpoint="second",
                        status="loaded",
                        stage="from_pretrained",
                        reason="fixture loaded",
                    ),
                ),
            )
        raise AssertionError("loader should stop before the third checkpoint")

    monkeypatch.setattr(
        task,
        "dependency_status",
        lambda: {
            "torch": "installed",
            "transformers": "installed",
            "huggingface_hub": "installed",
            "torchvision": "installed",
            "PIL": "installed",
            "numpy": "installed",
        },
    )
    monkeypatch.setattr(task, "_try_load_hf_vjepa2_encoder", fake_load)

    result = task.try_load_public_encoder(checkpoints=("first", "second", "third"), device="fixture-device")

    assert result.encoder is loaded
    assert calls == [("first", "fixture-device"), ("second", "fixture-device")]
    assert [(attempt.checkpoint, attempt.status, attempt.stage) for attempt in result.attempts] == [
        ("first", "failed", "from_pretrained"),
        ("second", "contacted", "config"),
        ("second", "loaded", "from_pretrained"),
    ]


def test_blocked_capsule_records_weight_acquisition_attempts():
    attempts = [
        task.WeightAttempt(
            checkpoint="facebook/vjepa2-vitl-fpc64-256",
            status="failed",
            reason="fixture unavailable",
        )
    ]
    original = task.try_load_public_encoder
    task.try_load_public_encoder = lambda *_args, **_kwargs: task.WeightLoadResult(None, attempts)
    try:
        payload = task.build_payload(generated_at="fixture", case_count=128, bootstrap_resamples=32)
    finally:
        task.try_load_public_encoder = original

    assert payload["execution_status"] == "blocked"
    assert payload["claim_boundary"]["status"] == "weight-acquisition-blocked"
    assert payload["weight_acquisition"]["status"] == "blocked"
    assert payload["weight_acquisition"]["attempts"][0]["checkpoint"] == "facebook/vjepa2-vitl-fpc64-256"
    assert payload["hardgate"]["gates"]["WEIGHT"]["status"] == "fail"
    assert payload["verdict"] == "blocked"


def test_loaded_encoder_payload_records_bounded_negative_base_chance_failure(monkeypatch):
    payload = _loaded_payload(monkeypatch, context_mode="constant-zero")

    assert payload["weight_acquisition"]["status"] == "loaded"
    assert payload["weight_acquisition"]["selected_checkpoint"] == "fixture/vjepa"
    assert payload["rank_eval"]["sample_count"] == 128
    assert payload["rank_eval"]["top1_accuracy"] == 0.125
    assert payload["base_chance_gate"]["status"] == "fail"
    assert payload["anti_triviality_controls"]["status"] == "pass"
    assert payload["execution_status"] == "bounded_negative"
    assert payload["failed_gate"] == "BASE-CHANCE"
    assert payload["claim_boundary"] == {"status": "bounded_negative", "failed_gate": "BASE-CHANCE"}
    assert payload["positive_claim"] == {"status": "bounded-negative", "positive_discovery": False, "level": "DN"}
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["WEIGHT"]["status"] == "pass"
    assert payload["hardgate"]["gates"]["BASE-CHANCE"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["CONTROL"]["status"] == "pass"


def test_loaded_encoder_payload_records_candidate_pass_when_rank_and_controls_clear(monkeypatch):
    payload = _loaded_payload(monkeypatch, context_mode="aligned")

    assert payload["weight_acquisition"]["status"] == "loaded"
    assert payload["rank_eval"]["sample_count"] == 128
    assert payload["rank_eval"]["top1_accuracy"] == 1.0
    assert payload["base_chance_gate"]["status"] == "pass"
    assert payload["anti_triviality_controls"]["status"] == "pass"
    assert payload["anti_triviality_controls"]["failed_controls"] == []
    assert payload["execution_status"] == "pass"
    assert payload["failed_gate"] is None
    assert payload["claim_boundary"] == {"status": "pass", "failed_gate": None}
    assert payload["positive_claim"] == {"status": "candidate-pass", "positive_discovery": True, "level": "D1"}
    assert payload["hardgate"]["status"] == "pass"
    assert payload["hardgate"]["gates"]["WEIGHT"]["status"] == "pass"
    assert payload["hardgate"]["gates"]["BASE-CHANCE"]["status"] == "pass"
    assert payload["hardgate"]["gates"]["CONTROL"]["status"] == "pass"


def test_loaded_encoder_payload_records_control_failure_after_base_chance_pass(monkeypatch):
    failing_controls = {
        "status": "fail",
        "failure_rule": "any control above empirical chance band fails the hardgate",
        "failed_controls": ["metadata_only"],
        "controls": {
            "metadata_only": {"status": "pass"},
            "no_context": {"status": "fail"},
            "shuffled_demo": {"status": "fail"},
        },
    }
    monkeypatch.setattr(task, "evaluate_controls", lambda *_args, **_kwargs: failing_controls)

    payload = _loaded_payload(monkeypatch, context_mode="aligned")

    assert payload["weight_acquisition"]["status"] == "loaded"
    assert payload["rank_eval"]["sample_count"] == 128
    assert payload["rank_eval"]["top1_accuracy"] == 1.0
    assert payload["base_chance_gate"]["status"] == "pass"
    assert payload["anti_triviality_controls"] == failing_controls
    assert payload["execution_status"] == "bounded_negative"
    assert payload["failed_gate"] == "CONTROL"
    assert payload["claim_boundary"] == {"status": "bounded_negative", "failed_gate": "CONTROL"}
    assert payload["positive_claim"] == {"status": "bounded-negative", "positive_discovery": False, "level": "DN"}
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["WEIGHT"]["status"] == "pass"
    assert payload["hardgate"]["gates"]["BASE-CHANCE"]["status"] == "pass"
    assert payload["hardgate"]["gates"]["CONTROL"]["status"] == "fail"


def test_gate_uses_ci_low_against_empirical_chance_ci_high_plus_margin():
    gate = task.base_chance_gate(
        base_cells=np.asarray([1.0] * 90 + [0.0] * 10),
        chance_components={
            "majority": np.asarray([1.0] * 55 + [0.0] * 45),
            "random": np.asarray([1.0] * 12 + [0.0] * 88),
        },
        seed=7,
        bootstrap_resamples=64,
    )

    assert gate["chance_selected_baseline"] == "majority"
    assert gate["status"] == "pass"
    assert gate["criterion"] == "base_ci95_low > empirical_chance_ci95_high + margin"
    assert gate["margin"] == task.BASE_CHANCE_MARGIN

    failed = task.base_chance_gate(
        base_cells=np.asarray([1.0] * 57 + [0.0] * 43),
        chance_components={
            "majority": np.asarray([1.0] * 55 + [0.0] * 45),
            "random": np.asarray([1.0] * 12 + [0.0] * 88),
        },
        seed=8,
        bootstrap_resamples=64,
    )
    assert failed["status"] == "fail"


def test_anti_trivial_controls_block_when_any_control_exceeds_chance_band():
    controls = task.evaluate_control_hardgate(
        {
            "metadata_only": task.base_chance_gate(
                np.asarray([1.0] * 40 + [0.0] * 60),
                {"random": np.asarray([1.0] * 12 + [0.0] * 88)},
                seed=1,
                bootstrap_resamples=32,
            ),
            "no_context": task.base_chance_gate(
                np.asarray([1.0] * 12 + [0.0] * 88),
                {"random": np.asarray([1.0] * 12 + [0.0] * 88)},
                seed=2,
                bootstrap_resamples=32,
            ),
            "shuffled_demo": task.base_chance_gate(
                np.asarray([1.0] * 10 + [0.0] * 90),
                {"random": np.asarray([1.0] * 12 + [0.0] * 88)},
                seed=3,
                bootstrap_resamples=32,
            ),
        }
    )

    assert controls["status"] == "fail"
    assert controls["failed_controls"] == ["metadata_only"]


def test_payload_writes_json_markdown_and_fingerprint(tmp_path):
    attempts = [
        task.WeightAttempt(
            checkpoint="facebook/vjepa2-vitl-fpc64-256",
            status="failed",
            reason="fixture unavailable",
        )
    ]

    json_path = tmp_path / task.JSON_ARTIFACT
    markdown_path = tmp_path / task.MARKDOWN_ARTIFACT
    fingerprint_path = tmp_path / task.FINGERPRINT_ARTIFACT
    original = task.try_load_public_encoder
    task.try_load_public_encoder = lambda *_args, **_kwargs: task.WeightLoadResult(None, attempts)
    try:
        payload = task.write_artifacts(
            root=tmp_path,
            json_path=json_path,
            markdown_path=markdown_path,
            fingerprint_path=fingerprint_path,
            generated_at="fixture",
            case_count=128,
            bootstrap_resamples=32,
        )
    finally:
        task.try_load_public_encoder = original

    assert json.loads(json_path.read_text(encoding="utf-8")) == payload
    assert markdown_path.read_text(encoding="utf-8").startswith("# JEPA-WM-L1 Micro-Admission")
    fingerprint = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    assert fingerprint["schema_id"] == task.FINGERPRINT_SCHEMA_ID
    assert fingerprint["json_artifact"] == task.JSON_ARTIFACT
    assert fingerprint["payload_sha256"] == task.canonical_digest(payload)
