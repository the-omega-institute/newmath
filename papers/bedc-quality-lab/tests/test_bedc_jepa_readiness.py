from bedc_quality_lab.bedc_jepa_readiness import build_bedc_jepa_readiness


def test_bedc_jepa_readiness_records_contact_gate_and_missing_public_evidence():
    readiness = build_bedc_jepa_readiness()

    assert readiness["schema_id"] == "bedc-jepa-readiness"
    assert readiness["decision"] in {"not_contact_ready", "contact_ready"}
    assert readiness["gates"]["torch_objective_seed_sweep"]["status"] == "pass"
    assert readiness["gates"]["local_visual_planning"]["status"] == "pass"
    assert readiness["gates"]["object_counterfactual_clutter"]["status"] == "pass"
    assert readiness["gates"]["public_minigrid_execution"]["status"] in {"pass", "missing"}
    assert readiness["gates"]["public_jepa_baseline"]["status"] in {"pass", "missing"}
    assert "public_minigrid_execution" in readiness["blocking_gates"]
    assert "public_jepa_baseline" in readiness["blocking_gates"]
    assert "install gymnasium/minigrid or run on an environment where both are present" in readiness["next_actions"]
