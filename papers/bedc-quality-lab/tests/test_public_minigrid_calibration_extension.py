from bedc_quality_lab.public_minigrid_calibration_extension import (
    DEFAULT_EXTENSION_SEEDS,
    DEFAULT_PLANNING_STATE_COUNTS,
    DEFAULT_TASK_VARIANTS,
    build_public_minigrid_calibration_extension,
)


def test_public_minigrid_calibration_extension_records_seed_budget_and_variant_rows():
    packet = build_public_minigrid_calibration_extension(
        seeds=(101,),
        task_variants=("MiniGrid-DoorKey-8x8-v0",),
        planning_state_counts=(2, 3),
        train_count=8,
        test_count=8,
    )

    assert packet["schema_id"] == "bedc-jepa-public-minigrid-calibration-extension"
    assert packet["status"] in {"executed", "source_gap"}
    assert packet["protocol"] == "public MiniGrid calibration and risk-success extension"
    assert packet["task_variants"] == ["MiniGrid-DoorKey-8x8-v0"]
    assert packet["seeds"] == [101.0]
    assert packet["planning_state_counts"] == [2.0, 3.0]
    assert len(packet["rows"]) == 2
    assert packet["summary"]["row_count"] == 2.0
    assert packet["summary"]["executed_row_count"] >= 0.0
    assert packet["summary"]["source_gap_row_count"] >= 0.0
    assert packet["summary"]["task_family_count"] == 1.0
    assert packet["summary"]["task_families"] == ["DoorKey"]
    for row in packet["rows"]:
        assert row["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
        assert row["task_family"] == "DoorKey"
        assert row["seed"] == 101.0
        assert row["claim_status"] in {
            "silent_debt_and_risk_direction",
            "silent_debt_direction",
            "risk_direction",
            "no_directional_gain",
            "source_gap",
        }
    assert "public benchmark superiority" in packet["cannot_claim"]


def test_public_minigrid_calibration_extension_defaults_cover_multiple_seeds_budgets_and_variants():
    assert len(DEFAULT_EXTENSION_SEEDS) >= 5
    assert len(DEFAULT_TASK_VARIANTS) >= 5
    assert len(DEFAULT_PLANNING_STATE_COUNTS) >= 3
    assert "MiniGrid-DoorKey-8x8-v0" in DEFAULT_TASK_VARIANTS
    assert "MiniGrid-Unlock-v0" in DEFAULT_TASK_VARIANTS
    assert "MiniGrid-KeyCorridorS3R1-v0" in DEFAULT_TASK_VARIANTS
    assert 32 in DEFAULT_PLANNING_STATE_COUNTS
