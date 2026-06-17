import json

import numpy as np

from bedc_quality_lab.tasks import jepa_wm_l1 as task


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
