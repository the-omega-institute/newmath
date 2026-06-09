from bedc_quality_lab.torch_bedc_jepa import run_torch_retraining_loss_ablation


def test_torch_retraining_loss_ablation_records_true_training_rows():
    packet = run_torch_retraining_loss_ablation(seeds=(101,), train_count=96, test_count=48, epochs=8)

    assert packet["schema_id"] == "bedc-jepa-retraining-loss-ablation"
    assert packet["status"] == "executed"
    assert packet["source"]["training"] == "torch-gradient-retraining"
    assert set(packet["systems"]) == {
        "full_s3",
        "minus_l_unlogged",
        "minus_l_gap",
        "minus_l_stab",
        "minus_l_intervention",
    }
    assert packet["systems"]["full_s3"]["status"] == "executed"
    assert packet["systems"]["minus_l_unlogged"]["status"] == "executed"
    assert packet["systems"]["minus_l_gap"]["status"] == "executed"
    assert packet["systems"]["minus_l_stab"]["status"] == "executed"
    assert packet["systems"]["minus_l_intervention"]["status"] == "executed"
    assert set(packet["supervision_surface_contract"]) == {"stability_consistency", "intervention_bce"}
    assert (
        "stability_source_split"
        in packet["supervision_surface_contract"]["stability_consistency"]["fields"]
    )
    assert (
        "intervention_source_split"
        in packet["supervision_surface_contract"]["intervention_bce"]["fields"]
    )
    assert "outside-gap OU pairs" in packet["supervision_surface_contract"]["stability_consistency"]["implemented_as"]
    assert "distinction_pair" in packet["supervision_surface_contract"]["intervention_bce"]["implemented_as"]
    assert len(packet["runs"]) == 5
    assert set(packet["summary"]) == {
        "full_s3",
        "minus_l_unlogged",
        "minus_l_gap",
        "minus_l_stab",
        "minus_l_intervention",
    }
    assert "full_s3_minus_minus_l_unlogged" in packet["comparisons"]
    assert "full_s3_minus_minus_l_gap" in packet["comparisons"]
    assert "full_s3_minus_minus_l_stab" in packet["comparisons"]
    assert "full_s3_minus_minus_l_intervention" in packet["comparisons"]

    for system_summary in packet["summary"].values():
        assert 0.0 <= system_summary["unlogged_error_rate_mean"] <= 1.0
        assert 0.0 <= system_summary["gap_detection_auc_mean"] <= 1.0
        assert 0.0 <= system_summary["bedc_debt_score_mean"] <= 1.0
