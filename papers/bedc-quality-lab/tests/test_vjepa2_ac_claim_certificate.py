import numpy as np

from bedc_quality_lab.vjepa2_ac_claim_certificate import build_vjepa2_ac_claim_certificate_packet


def test_vjepa2_ac_claim_certificate_packet_is_fail_closed():
    rng = np.random.default_rng(20260610)
    features = rng.normal(size=(96, 6))
    labels = features[:, 0] + 0.5 * features[:, 1] > 0.0
    gaps = np.abs(features[:, 0]) < 0.35

    packet = build_vjepa2_ac_claim_certificate_packet(
        features_train=features[:32],
        labels_train=labels[:32],
        gaps_train=gaps[:32],
        features_calibration=features[32:64],
        labels_calibration=labels[32:64],
        gaps_calibration=gaps[32:64],
        features_test=features[64:],
        labels_test=labels[64:],
        gaps_test=gaps[64:],
        torch_environment={"cuda_available": True, "cuda_device_name": "test-device"},
    )

    assert packet["schema_id"] == "bedc-vjepa2-ac-minigrid-claim-certificate"
    assert packet["status"] == "executed"
    assert packet["carrier_id"] == "vjepa2-ac-giant-fixed-minigrid-carrier"
    assert packet["torch_environment"]["cuda_device_name"] == "test-device"
    assert packet["execution_contract"]["run_command"] == "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py"
    assert "LCCP readback" in packet["execution_contract"]["split_rule"]
    assert packet["checkpoint_contract"]["repository_url"] == "https://github.com/facebookresearch/vjepa2"
    assert packet["checkpoint_contract"]["hub_entry"] == "vjepa2_ac_vit_giant"
    assert packet["checkpoint_contract"]["checkpoint_url"].endswith("/vjepa2-ac-vitg.pt")
    assert packet["checkpoint_contract"]["loaded_components"] == ["encoder", "predictor"]
    assert "action-conditioned predictor pooled token features" in packet["feature_contract"]["carrier_features"]
    assert "split conformal singleton claims" in packet["feature_contract"]["certificate_protocol"]
    assert {claim["predicate"] for claim in packet["claims"]} == {
        "door_key_context_visible",
        "unsafe_transition",
        "has_key",
        "door_open_or_unlocked",
        "goal_reachable_with_current_state",
    }
    for claim in packet["claims"]:
        assert claim["claim_status"] in {"certified", "coverage_gap", "source_gap"}
        if claim["claim_status"] == "source_gap":
            assert claim["debt_decomposition"]["source_debt"] == 1.0
        else:
            assert len(claim["sweep"]) == 5
            assert 0.0 <= claim["primary"]["certified_coverage"] <= 1.0
            assert 0.0 <= claim["primary"]["unlogged_error"] <= 1.0
    assert packet["accepted_claim_count"] + packet["gap_claim_count"] == float(len(packet["claims"]))
