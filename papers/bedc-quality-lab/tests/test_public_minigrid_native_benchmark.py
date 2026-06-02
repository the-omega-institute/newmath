from bedc_quality_lab.public_minigrid_native_benchmark import (
    build_public_minigrid_native_benchmark,
    build_public_minigrid_native_seed_sweep,
)


def test_public_minigrid_native_benchmark_fails_closed_or_records_full_contract():
    packet = build_public_minigrid_native_benchmark(train_count=8, test_count=8, planning_state_count=4, seed=17)

    assert packet["schema_id"] == "bedc-jepa-public-native-minigrid-benchmark"
    assert packet["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert packet["status"] in {"executed", "unavailable"}
    assert set(packet["dependency_status"]) == {"gymnasium", "minigrid"}

    if packet["status"] == "unavailable":
        assert packet["sample_count_collected"] == 0.0
        assert packet["systems"] == {}
        assert packet["planning_lambda_sweep"] == []
        assert "native public MiniGrid benchmark was not executed in this environment" in packet["cannot_claim"]
        return

    assert packet["sample_count_collected"] == 16.0
    assert packet["train_count"] == 8.0
    assert packet["test_count"] == 8.0
    assert set(packet["systems"]) == {"S0", "S1", "S2", "S3"}
    assert packet["systems"]["S3"]["changes_training_objective"] == 1.0
    for system in packet["systems"].values():
        assert 0.0 <= system["distinction_accuracy"] <= 1.0
        assert 0.0 <= system["gap_detection_auc"] <= 1.0
        assert 0.0 <= system["unlogged_error_rate"] <= 1.0
        assert 0.0 <= system["certified_coverage"] <= 1.0
        assert 0.0 <= system["bedc_debt_score"] <= 1.0
    assert len(packet["planning_lambda_sweep"]) == 5
    assert packet["planning_lambda_sweep"][0]["lambda_g"] == 0.0
    assert packet["planning_lambda_sweep"][-1]["lambda_g"] == 4.0
    assert packet["jepa_family_baseline_boundary"]["status"] == "executed"
    assert packet["jepa_family_baseline_boundary"]["reported_benchmark_name"] == "MiniGrid-DoorKey-8x8-v0"
    assert "native V-JEPA2-AC checkpoint reproduction" in packet["cannot_claim"]


def test_public_minigrid_native_benchmark_records_gap_aware_planning_tradeoff_when_available():
    packet = build_public_minigrid_native_benchmark(train_count=32, test_count=32, planning_state_count=8, seed=23)

    if packet["status"] == "unavailable":
        assert packet["systems"] == {}
        return

    lambdas = [row["lambda_g"] for row in packet["planning_lambda_sweep"]]
    assert lambdas == [0.0, 0.5, 1.0, 2.0, 4.0]
    assert packet["planning_state_count_collected"] == 8.0
    assert set(packet["deltas"]) == {
        "s3_minus_s0_distinction_accuracy",
        "s3_minus_s0_gap_auc",
        "s0_minus_s3_unlogged_error",
        "s0_minus_s3_debt",
        "lambda_0_minus_best_high_gap_rate",
        "lambda_0_minus_best_success_rate",
        "best_planning_lambda_g",
    }
    for row in packet["planning_lambda_sweep"]:
        assert 0.0 <= row["success_rate"] <= 1.0
        assert 0.0 <= row["high_gap_state_rate"] <= 1.0
        assert row["risk_adjusted_cost"] >= 0.0


def test_public_minigrid_native_seed_sweep_records_summary_or_dependency_boundary():
    packet = build_public_minigrid_native_seed_sweep(seeds=(101, 102), train_count=8, test_count=8, planning_state_count=4)

    assert packet["schema_id"] == "bedc-jepa-public-native-minigrid-seed-sweep"
    assert packet["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert packet["seed_count_requested"] == 2.0
    assert packet["status"] in {"executed", "unavailable"}

    if packet["status"] == "unavailable":
        assert packet["seed_count_executed"] < packet["seed_count_requested"]
        assert packet["summary"] == {}
        return

    assert packet["seed_count_executed"] == 2.0
    assert len(packet["packets"]) == 2
    summary = packet["summary"]
    assert summary["seed_count"] == 2.0
    for key in (
        "s0_minus_s3_unlogged_error_mean",
        "s3_minus_s0_gap_auc_mean",
        "s0_minus_s3_debt_mean",
        "lambda_0_minus_best_high_gap_rate_mean",
        "lambda_0_minus_best_success_rate_mean",
        "unlogged_error_win_rate",
        "gap_auc_win_rate",
        "debt_win_rate",
        "planning_high_gap_reduction_win_rate",
    ):
        assert key in summary
