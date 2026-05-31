from bedc_quality_lab.public_minigrid_adapter import (
    build_public_minigrid_probe,
    build_public_minigrid_transition_packet,
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
