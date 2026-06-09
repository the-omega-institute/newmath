import json

import pytest

from bedc_quality_lab import dgt_l0_controls
from bedc_quality_lab.dgt_l0_controls import (
    CANONICAL_JSON_ARTIFACT,
    CONTROL_POINTERS,
    rebuild_l0_projection,
    validate_payload,
)


def _payload():
    return dgt_l0_controls.build_payload(generated_at="fixture-time", requested_device="cpu")


def test_dgt_l0_controls_true_training_payload_is_ready():
    payload = _payload()

    assert payload["schema_id"] == "bedc-quality-lab:dgt-l0-controls"
    assert payload["artifact_id"] == "bedc-quality-lab:dgt-l0-controls"
    assert payload["l0_toy_projection"]["review_status"] == "ready"
    assert payload["l0_toy_projection"]["ref_pointers"] == CONTROL_POINTERS
    assert payload["controls"]["base_transformer_control"]["loss_decrease"] > 0
    assert payload["controls"]["base_transformer_control"]["parameter_l2_delta"] > 0
    assert payload["controls"]["matched_random_structural_control"]["classifier_shift_count"] == 0
    assert payload["compute_param_ledger"]["compute_units"] > 0
    assert payload["compute_param_ledger"]["parameter_count"] > 0
    assert payload["negative_witness_sweep"]["critical_hit_count"] == 0
    assert payload["independent_replay"]["comparisons"]["dgt_quality_ci_low_gt_base"] is True
    assert payload["independent_replay"]["comparisons"]["dgt_uer_reduction_gt_matched_random"] is True


def test_dgt_l0_controls_writes_run_local_cache_without_authority(tmp_path):
    payload = _payload()
    dgt_l0_controls.write_artifacts(payload, root=tmp_path, generated_at="fixture-time")

    canonical_payload = json.loads((tmp_path / CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))
    claim_capsule = json.loads(
        (tmp_path / "reports/runs/discovery-gated-transformer/l0-toy-controls/claim_capsule.json").read_text(
            encoding="utf-8"
        )
    )
    fingerprint = json.loads((tmp_path / "reports/canonical/dgt-l0-controls.fingerprint.json").read_text(encoding="utf-8"))

    assert canonical_payload["l0_toy_projection"]["review_status"] == "ready"
    assert claim_capsule["owner_artifact"] == CANONICAL_JSON_ARTIFACT
    assert claim_capsule["owner_pointer"] == f"{CANONICAL_JSON_ARTIFACT}:$.l0_toy_projection"
    assert "run_local_cache" in fingerprint["inputs"]
    assert "reports/runs/discovery-gated-transformer/l0-toy-controls/claim_capsule.json" in json.dumps(fingerprint)


@pytest.mark.parametrize(
    ("group", "mutate", "expected_gate"),
    [
        ("L0", lambda payload: payload["controls"]["base_transformer_control"].update({"status": "fail"}), "L0-HG1"),
        ("base", lambda payload: payload["controls"]["base_transformer_control"].update({"loss_decrease": 0.0}), "BASE-L0-HG4"),
        (
            "matched_random",
            lambda payload: payload["controls"]["matched_random_structural_control"].update({"classifier_shift_count": 1}),
            "MR-L0-HG6",
        ),
        ("ledger", lambda payload: payload["compute_param_ledger"].update({"compute_units": 0}), "LEDGER-L0-HG4"),
        ("negative_witness", lambda payload: payload["negative_witness_sweep"].update({"critical_hit_count": 1}), "NW-L0-HG3"),
        (
            "replay",
            lambda payload: payload["independent_replay"]["comparisons"].update({"dgt_quality_ci_low_gt_base": False}),
            "REPLAY-L0-HG4",
        ),
        (
            "pointer",
            lambda payload: payload["l0_toy_projection"]["ref_pointers"]["base_transformer_control"].update(
                {"pointer": "$.missing"}
            ),
            "PTR-HG1",
        ),
    ],
)
def test_dgt_l0_controls_each_gate_group_fails_closed(group, mutate, expected_gate):
    payload = _payload()
    mutate(payload)
    payload["l0_toy_projection"] = rebuild_l0_projection(payload)

    assert payload["l0_toy_projection"]["review_status"] == "blocked"
    assert payload["l0_toy_projection"]["hardgate_statuses"][group]["gates"][expected_gate]["status"] == "fail"
    assert f"{group}:{expected_gate}" in payload["l0_toy_projection"]["failure_reasons"]


def test_dgt_l0_controls_rejects_stale_projection_after_mutation():
    payload = _payload()
    payload["compute_param_ledger"]["parameter_count"] = 0

    with pytest.raises(ValueError, match="hardgate evaluation|positive compute"):
        validate_payload(payload)
