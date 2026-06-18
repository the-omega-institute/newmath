import json

from bedc_quality_lab.bedc_multistep_latent_prediction import (
    LatentPredictionGateSpec,
    LatentRolloutBatch,
    PredictorSpec,
    run_multistep_latent_prediction_smoke,
)


def test_multistep_latent_prediction_packet_is_json_primitive_and_fail_closed():
    packet = run_multistep_latent_prediction_smoke(sample_count=16, horizon=3, seed=13)

    json.dumps(packet)
    assert packet["schema_id"] == "bedc-multistep-latent-prediction"
    assert packet["status"] == "executed"
    assert packet["record_scope"] == "local_smoke_contract"
    assert packet["evidence_chain"]["owner_module"] == (
        "bedc_quality_lab.bedc_multistep_latent_prediction"
    )
    assert packet["rollout_contract"]["sample_count"] == 16
    assert packet["rollout_contract"]["horizon"] == 3
    assert packet["rollout_batch"] == packet["rollout_contract"]
    assert {row["family"] for row in packet["predictor_specs"]} == {
        "jepa_mlp",
        "gru",
        "rssm",
        "transformer",
    }
    assert {row["horizon"] for row in packet["runs"]} == {1, 3}
    assert any(row["action_conditioned"] for row in packet["runs"])
    assert all(row["planning_success"] is None for row in packet["runs"])
    assert packet["summary"]["run_count"] == len(packet["runs"])
    assert packet["summary"]["family_count"] == 4
    assert packet["summary"]["planning_success_claimed"] is False
    assert packet["predictor_spec"]["predictor_id"] == packet["predictor_specs"][0]["predictor_id"]
    assert packet["predictor_spec"]["training_status"] == "deterministic_smoke_baseline"
    assert packet["gate_spec"]["status"] in {"pass", "source_debt"}
    assert packet["hardgate"] == packet["gate_spec"]
    assert "rollout_contract" in packet["gate_spec"]["required_record_fields"]
    assert "predictor_specs" in packet["gate_spec"]["required_record_fields"]
    assert "runs" in packet["gate_spec"]["required_record_fields"]
    assert packet["metrics"]["rollout_mse"] >= 0.0
    assert 0.0 <= packet["metrics"]["latent_prediction_score"] <= 1.0
    assert 0.0 <= packet["metrics"]["gap_detection_auc"] <= 1.0
    assert 0.0 <= packet["metrics"]["certified_coverage"] <= 1.0
    assert 0.0 <= packet["metrics"]["unlogged_error_rate"] <= 1.0
    assert packet["claim_scope"]["minigrid_planning_success"] == "not_claimed"
    assert packet["claim_scope"]["full_4090_sweep"] == "not_claimed"
    assert "MiniGrid planning success" in packet["cannot_claim"]
    assert "quality backend full-sweep admission" in packet["cannot_claim"]


def test_multistep_latent_prediction_schema_owner_types_are_local():
    assert LatentRolloutBatch.__module__ == "bedc_quality_lab.bedc_multistep_latent_prediction"
    assert PredictorSpec.__module__ == "bedc_quality_lab.bedc_multistep_latent_prediction"
    assert LatentPredictionGateSpec.__module__ == (
        "bedc_quality_lab.bedc_multistep_latent_prediction"
    )
