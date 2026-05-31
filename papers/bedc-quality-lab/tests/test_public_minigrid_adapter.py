from bedc_quality_lab.public_minigrid_adapter import (
    build_public_minigrid_external_result,
    build_public_minigrid_benchmark_packet,
    build_public_minigrid_probe,
    build_public_minigrid_transition_packet,
    import_public_minigrid_benchmark_metrics,
)


def test_public_minigrid_probe_records_dependency_boundary():
    probe = build_public_minigrid_probe()

    assert probe.environment_id == "MiniGrid-DoorKey-8x8-v0"
    assert probe.observation_contract.startswith("Gymnasium")
    assert probe.action_contract.startswith("Discrete MiniGrid")
    assert set(probe.dependency_status) == {"gymnasium", "minigrid"}
    assert probe.status in {"available", "unavailable"}

    if probe.status == "available":
        assert probe.cannot_claim == []
    else:
        assert "public MiniGrid run was not executed in this environment" in probe.cannot_claim


def test_public_minigrid_transition_packet_has_executable_contract():
    packet = build_public_minigrid_transition_packet(sample_count=4, seed=17)

    assert packet["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert packet["sample_count_requested"] == 4.0
    assert packet["seed"] == 17.0
    assert packet["observation_key"] == "image"
    assert packet["observation_shape_contract"] == [7.0, 7.0, 3.0]
    assert packet["action_space_contract"] == "Discrete"
    assert packet["status"] in {"available", "unavailable"}

    if packet["status"] == "available":
        assert packet["sample_count_collected"] == 4.0
        assert len(packet["transition_samples"]) == 4
        assert {"action", "reward", "terminated", "truncated", "image_checksum", "next_image_checksum"} <= set(
            packet["transition_samples"][0]
        )
        assert packet["cannot_claim"] == []
    else:
        assert packet["sample_count_collected"] == 0.0
        assert packet["transition_samples"] == []
        assert "public MiniGrid run was not executed in this environment" in packet["cannot_claim"]


def test_public_minigrid_benchmark_packet_has_metric_contract():
    packet = build_public_minigrid_benchmark_packet(sample_count=4, seed=17)

    assert packet["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert packet["benchmark_contract"] == "door-key-public-readback-gap"
    assert packet["sample_count_requested"] == 4.0
    assert packet["status"] in {"available", "unavailable"}
    assert set(packet["metrics"]) == {
        "distinction_accuracy",
        "gap_detection_auc",
        "unlogged_error_rate",
        "certified_coverage",
        "bedc_debt_score",
    }

    if packet["status"] == "available":
        assert packet["sample_count_collected"] == 4.0
        assert packet["metrics"]["distinction_accuracy"] >= 0.0
        assert packet["metrics"]["gap_detection_auc"] >= 0.0
        assert packet["cannot_claim"] == []
    else:
        assert packet["sample_count_collected"] == 0.0
        assert packet["metrics"]["bedc_debt_score"] is None
        assert "public MiniGrid benchmark was not executed in this environment" in packet["cannot_claim"]


def test_public_minigrid_metrics_import_marks_benchmark_available():
    packet = import_public_minigrid_benchmark_metrics(
        {
            "environment_id": "MiniGrid-DoorKey-8x8-v0",
            "seed": 31,
            "sample_count_requested": 32,
            "sample_count_collected": 32,
            "distinction_accuracy": 0.91,
            "gap_detection_auc": 0.83,
            "unlogged_error_rate": 0.04,
            "certified_coverage": 0.72,
            "bedc_debt_score": 0.11,
        }
    )

    assert packet["status"] == "available"
    assert packet["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert packet["sample_count_collected"] == 32.0
    assert packet["metrics"] == {
        "distinction_accuracy": 0.91,
        "gap_detection_auc": 0.83,
        "unlogged_error_rate": 0.04,
        "certified_coverage": 0.72,
        "bedc_debt_score": 0.11,
    }
    assert packet["cannot_claim"] == []


def test_public_minigrid_external_result_exports_importer_schema_or_dependency_boundary():
    result = build_public_minigrid_external_result(sample_count=4, seed=17)

    assert result["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert result["seed"] == 17.0
    assert result["sample_count_requested"] == 4.0

    if result["status"] == "available":
        assert set(result) == {
            "status",
            "environment_id",
            "seed",
            "sample_count_requested",
            "sample_count_collected",
            "distinction_accuracy",
            "gap_detection_auc",
            "unlogged_error_rate",
            "certified_coverage",
            "bedc_debt_score",
        }
        packet = import_public_minigrid_benchmark_metrics(result)
        assert packet["status"] == "available"
        assert packet["sample_count_collected"] == 4.0
    else:
        assert result["status"] == "unavailable"
        assert result["sample_count_collected"] == 0.0
        assert result["cannot_export"] == ["public MiniGrid benchmark was not executed in this environment"]
