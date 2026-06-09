import numpy as np

from bedc_quality_lab.vjepa2_ac_latent_prediction import build_vjepa2_ac_latent_prediction_packet


def test_vjepa2_ac_latent_prediction_packet_records_contact_metrics():
    rng = np.random.default_rng(20260610)
    source = rng.normal(size=(48, 8))
    predicted = source @ np.eye(8) + 0.05 * rng.normal(size=(48, 8))

    packet = build_vjepa2_ac_latent_prediction_packet(
        source_features=source,
        predicted_features=predicted,
        train_count=32,
        torch_environment={"cuda_available": True, "gpu_name": "test-device"},
        dependency_status={"torch": "installed"},
    )

    assert packet["schema_id"] == "bedc-vjepa2-ac-minigrid-latent-prediction"
    assert packet["status"] == "executed"
    assert packet["candidate_id"] == "vjepa2-ac-vit-giant"
    assert packet["carrier_id"] == "vjepa2-ac-giant-fixed-minigrid-carrier"
    assert packet["sample_counts"]["train"] == 32.0
    assert packet["sample_counts"]["test"] == 16.0
    assert packet["feature_dimension"] == 8.0
    assert packet["metrics"]["linear_aligned_r2"] > 0.95
    assert packet["metrics"]["latent_prediction_score"] > 0.95
    assert packet["metrics"]["flattened_correlation"] > 0.95
    assert "official V-JEPA2-AC benchmark reproduction" in packet["cannot_claim"]


def test_vjepa2_ac_latent_prediction_rejects_bad_shapes():
    source = np.zeros((8, 3))
    predicted = np.zeros((8, 4))
    try:
        build_vjepa2_ac_latent_prediction_packet(
            source_features=source,
            predicted_features=predicted,
            train_count=4,
        )
    except ValueError as exc:
        assert "same shape" in str(exc)
    else:
        raise AssertionError("expected ValueError")
