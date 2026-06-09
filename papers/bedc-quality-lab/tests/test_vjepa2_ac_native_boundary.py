from bedc_quality_lab.vjepa2_ac_native_boundary import build_vjepa2_ac_native_boundary


def test_vjepa2_ac_native_boundary_is_fail_closed():
    packet = build_vjepa2_ac_native_boundary()

    assert packet["schema_id"] == "bedc-jepa-vjepa2-ac-native-boundary"
    assert packet["status"] == "not_executed"
    assert packet["native_reproduction_status"] == "not_evaluated"
    assert packet["fixed_checkpoint_latent_prediction_status"] == "executed"
    assert packet["candidate_id"] == "vjepa2-ac-vit-giant"
    assert packet["target_public_benchmark"] == "MiniGrid-DoorKey-8x8-v0"
    assert "reports/bedc_jepa_public_ac_giant_adapter.json" in packet["current_contact_artifacts"]
    assert "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json" in packet["current_contact_artifacts"]
    assert "official V-JEPA2-AC benchmark reproduction" in packet["blocking_boundary"]
    assert "native V-JEPA2-AC benchmark reproduction" in packet["cannot_claim"]
