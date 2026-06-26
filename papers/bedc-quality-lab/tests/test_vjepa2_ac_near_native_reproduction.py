from bedc_quality_lab.vjepa2_ac_near_native_reproduction import (
    build_vjepa2_ac_native_readback_comparison,
    build_vjepa2_ac_near_native_reproduction,
)


def test_vjepa2_ac_near_native_reproduction_records_fail_closed_boundary():
    packet = build_vjepa2_ac_near_native_reproduction()

    assert packet["schema_id"] == "bedc-vjepa2-ac-near-native-minigrid-reproduction"
    assert packet["status"] == "evaluated_near_native"
    assert packet["official_native_reproduction_status"] == "not_evaluated"
    assert packet["near_native_protocol_status"] == "executed"
    assert packet["candidate_id"] == "vjepa2-ac-vit-giant"
    assert packet["public_environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert packet["vjepa2_repository_commit"] == "204698b45b3712590f06245fbfba32d3be539812"
    assert packet["repository_identity"]["repository_url"] == "https://github.com/facebookresearch/vjepa2"
    assert packet["repository_identity"]["identity_command"] == (
        "git ls-remote https://github.com/facebookresearch/vjepa2 HEAD"
    )
    assert packet["native_or_near_native_rollout_score"]["score_name"] == (
        "fixed_checkpoint_latent_prediction_score"
    )
    assert packet["native_or_near_native_rollout_score"]["official_rollout_score_status"] == "not_evaluated"
    assert packet["latent_prediction_score"] > 0.0
    assert "latent_prediction" in packet["image_action_stream_split"]
    assert "lccp_certificate" in packet["image_action_stream_split"]
    assert "public_environment_id" in packet
    assert "execution_command" in packet
    assert "bedc_readback_metrics" in packet
    assert "lccp_certificate_metrics" in packet
    assert packet["bedc_readback_metrics"]["predicate_count"] >= 1.0
    assert packet["lccp_certificate_metrics"]["status"] in {"executed", "source_gap"}
    assert "same_train_cal_test_split" in packet["parity_protocol"]
    assert packet["parity_gaps"]
    assert packet["claim_status"] == "near_native_fixed_checkpoint_record_with_official_reproduction_gap"
    assert "official V-JEPA2-AC benchmark reproduction" in packet["cannot_claim_boundary"]
    assert "public benchmark superiority" in packet["cannot_claim_boundary"]
    assert "checkpoint native evaluation parity" in packet["cannot_claim_boundary"]


def test_vjepa2_ac_native_readback_comparison_does_not_assert_superiority():
    comparison = build_vjepa2_ac_native_readback_comparison()

    assert comparison["schema_id"] == "bedc-vjepa2-ac-native-readback-comparison"
    assert comparison["status"] == "evaluated_near_native"
    assert comparison["official_native_reproduction_status"] == "not_evaluated"
    assert comparison["vjepa2_ac_fixed_checkpoint"]["latent_prediction_score"] > 0.0
    assert comparison["bedc_jepa_public_minigrid"]["s0_unlogged_error"] >= 0.0
    assert comparison["bedc_jepa_public_minigrid"]["s3_unlogged_error"] >= 0.0
    assert "does not assert" in comparison["claim_rule"]
    assert "official V-JEPA2-AC benchmark reproduction" in comparison["cannot_claim_boundary"]
