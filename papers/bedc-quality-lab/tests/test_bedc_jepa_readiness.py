from bedc_quality_lab.bedc_jepa_readiness import build_bedc_jepa_readiness, _public_minigrid_gate


def test_bedc_jepa_readiness_records_contact_gate_and_missing_public_evidence():
    readiness = build_bedc_jepa_readiness()

    assert readiness["schema_id"] == "bedc-jepa-readiness"
    assert readiness["decision"] in {"not_contact_ready", "contact_ready"}
    assert readiness["gates"]["torch_objective_seed_sweep"]["status"] == "pass"
    assert readiness["gates"]["local_visual_planning"]["status"] == "pass"
    assert readiness["gates"]["object_counterfactual_clutter"]["status"] == "pass"
    assert readiness["gates"]["public_minigrid_execution"]["status"] in {"pass", "missing"}
    assert readiness["gates"]["public_jepa_baseline"]["status"] in {"pass", "missing"}
    if readiness["gates"]["public_minigrid_execution"]["status"] == "pass":
        assert "public_minigrid_execution" not in readiness["blocking_gates"]
    else:
        assert "public_minigrid_execution" in readiness["blocking_gates"]
    assert "public_jepa_baseline" in readiness["blocking_gates"]
    assert "install gymnasium/minigrid or run on an environment where both are present" in readiness["next_actions"]


def test_public_minigrid_readiness_accepts_externally_executed_packet():
    gate = _public_minigrid_gate(
        {
            "status": "available",
            "sample_count_collected": 32.0,
            "dependency_status": {
                "gymnasium": "external-executed",
                "minigrid": "external-executed",
            },
        }
    )

    assert gate["status"] == "pass"
