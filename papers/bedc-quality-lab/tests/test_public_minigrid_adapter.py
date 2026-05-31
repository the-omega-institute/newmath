from bedc_quality_lab.public_minigrid_adapter import build_public_minigrid_probe


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
