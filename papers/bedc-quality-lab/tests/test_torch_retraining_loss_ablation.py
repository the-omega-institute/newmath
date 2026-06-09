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
    assert packet["systems"]["minus_l_stab"]["status"] == "source_debt"
    assert packet["systems"]["minus_l_intervention"]["status"] == "source_debt"
    assert len(packet["runs"]) == 3
    assert set(packet["summary"]) == {"full_s3", "minus_l_unlogged", "minus_l_gap"}
    assert "full_s3_minus_minus_l_unlogged" in packet["comparisons"]
    assert "full_s3_minus_minus_l_gap" in packet["comparisons"]

    for system_summary in packet["summary"].values():
        assert 0.0 <= system_summary["unlogged_error_rate_mean"] <= 1.0
        assert 0.0 <= system_summary["gap_detection_auc_mean"] <= 1.0
        assert 0.0 <= system_summary["bedc_debt_score_mean"] <= 1.0
