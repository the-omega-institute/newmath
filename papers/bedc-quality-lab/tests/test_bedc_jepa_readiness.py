from bedc_quality_lab.bedc_jepa_readiness import build_bedc_jepa_readiness, _public_minigrid_gate


def test_bedc_jepa_readiness_records_checkpoint_contact_and_open_native_gate():
    readiness = build_bedc_jepa_readiness()

    assert readiness["schema_id"] == "bedc-jepa-readiness"
    assert readiness["decision"] in {
        "contact_boundary_open",
        "native_public_benchmark_closed_artifact_bundle_open",
        "external_bundle_ready",
    }
    assert readiness["evidence_boundary"]["checkpoint_contact"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["native_public_benchmark"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["artifact_review_bundle"] in {"closed", "open"}
    assert readiness["gates"]["torch_objective_seed_sweep"]["status"] == "pass"
    assert readiness["gates"]["local_visual_planning"]["status"] == "pass"
    assert readiness["gates"]["object_counterfactual_clutter"]["status"] == "pass"
    assert readiness["gates"]["public_minigrid_execution"]["status"] in {"pass", "missing"}
    assert readiness["gates"]["public_jepa_checkpoint_contact"]["status"] == "pass"
    assert readiness["gates"]["native_public_jepa_benchmark"]["status"] == "pass"
    assert readiness["gates"]["artifact_review_bundle"]["status"] == "pass"
    if readiness["gates"]["public_minigrid_execution"]["status"] == "pass":
        assert "public_minigrid_execution" not in readiness["blocking_gates"]
    else:
        assert "public_minigrid_execution" in readiness["blocking_gates"]
    assert "public_jepa_checkpoint_contact" not in readiness["blocking_gates"]
    assert "native_public_jepa_benchmark" not in readiness["blocking_gates"]
    assert "artifact_review_bundle" not in readiness["blocking_gates"]
    assert readiness["blocking_gates"] == []
    assert readiness["evidence_boundary"] == {
        "checkpoint_contact": "closed",
        "native_public_benchmark": "closed",
        "artifact_review_bundle": "closed",
    }
    assert (
        "run native V-JEPA2-AC latent-prediction or rollout protocol on the public MiniGrid observation/action stream"
        in readiness["next_actions"]
    )


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
