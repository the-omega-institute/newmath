from bedc_quality_lab.bedc_jepa_readiness import build_bedc_jepa_readiness, _public_minigrid_gate


def test_bedc_jepa_readiness_records_checkpoint_evaluation_and_open_native_gate():
    readiness = build_bedc_jepa_readiness()

    assert readiness["schema_id"] == "bedc-jepa-readiness"
    assert readiness["decision"] in {
        "evidence_boundary_open",
        "native_public_benchmark_closed_artifact_bundle_open",
        "external_bundle_ready",
    }
    assert readiness["evidence_boundary"]["checkpoint_evaluation"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["vjepa2_ac_minigrid_latent_prediction"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["native_public_benchmark"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["artifact_review_bundle"] in {"closed", "open"}
    assert readiness["gates"]["torch_objective_seed_sweep"]["status"] == "pass"
    assert readiness["gates"]["local_visual_planning"]["status"] == "pass"
    assert readiness["gates"]["object_counterfactual_clutter"]["status"] == "pass"
    assert readiness["gates"]["public_minigrid_execution"]["status"] in {"pass", "missing"}
    assert readiness["gates"]["public_jepa_checkpoint_evaluation"]["status"] == "pass"
    assert readiness["gates"]["vjepa2_ac_minigrid_latent_prediction"]["status"] == "pass"
    assert readiness["gates"]["native_public_jepa_benchmark"]["status"] == "pass"
    assert readiness["gates"]["artifact_review_bundle"]["status"] == "pass"
    if readiness["gates"]["public_minigrid_execution"]["status"] == "pass":
        assert "public_minigrid_execution" not in readiness["blocking_gates"]
    else:
        assert "public_minigrid_execution" in readiness["blocking_gates"]
    assert "public_jepa_checkpoint_evaluation" not in readiness["blocking_gates"]
    assert "vjepa2_ac_minigrid_latent_prediction" not in readiness["blocking_gates"]
    assert "native_public_jepa_benchmark" not in readiness["blocking_gates"]
    assert "artifact_review_bundle" not in readiness["blocking_gates"]
    assert readiness["blocking_gates"] == []
    assert readiness["evidence_boundary"] == {
        "checkpoint_evaluation": "closed",
        "vjepa2_ac_minigrid_latent_prediction": "closed",
        "native_public_benchmark": "closed",
        "artifact_review_bundle": "closed",
    }
    remaining = readiness["remaining_evidence_contracts"]
    retraining = remaining["true_retraining_loss_ablation"]
    native = remaining["vjepa2_ac_native_reproduction"]
    assert retraining["status"] == "source_surfaces_required"
    assert retraining["executed_rows"] == ["full_s3", "minus_l_gap", "minus_l_unlogged"]
    assert retraining["source_debt_rows"] == ["minus_l_intervention", "minus_l_stab"]
    assert "minus_l_stab" in retraining["source_debt_contract"]
    assert "minus_l_intervention" in retraining["source_debt_contract"]
    assert native["status"] == "not_evaluated"
    assert "native_acceptance_contract" in native
    assert "required_native_evidence" in native["native_acceptance_contract"]
    assert (
        "run an official V-JEPA2-AC benchmark reproduction or rollout benchmark beyond the fixed-checkpoint MiniGrid studies"
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
