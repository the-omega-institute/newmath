import json

import numpy as np

from bedc_quality_lab.tasks import jepa_wm_l1 as task


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
