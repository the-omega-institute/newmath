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
    assert readiness["evidence_boundary"]["vjepa2_ac_near_native_reproduction"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["native_public_benchmark"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["public_minigrid_calibration_pareto"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["public_minigrid_calibration_extension"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["public_baseline_native_metric_contract"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["public_baseline_native_metric_template"] in {"closed", "open"}
    assert readiness["evidence_boundary"]["artifact_review_bundle"] in {"closed", "open"}
    assert readiness["gates"]["torch_objective_seed_sweep"]["status"] == "pass"
    assert readiness["gates"]["local_visual_planning"]["status"] == "pass"
    assert readiness["gates"]["object_counterfactual_clutter"]["status"] == "pass"
    assert readiness["gates"]["public_minigrid_execution"]["status"] in {"pass", "missing"}
    assert readiness["gates"]["public_jepa_checkpoint_evaluation"]["status"] == "pass"
    assert readiness["gates"]["vjepa2_ac_minigrid_latent_prediction"]["status"] == "pass"
    assert readiness["gates"]["vjepa2_ac_near_native_reproduction"]["status"] == "pass"
    assert readiness["gates"]["public_minigrid_calibration_pareto"]["status"] == "pass"
    assert readiness["gates"]["public_minigrid_calibration_extension"]["status"] == "pass"
    assert readiness["gates"]["public_baseline_native_metric_contract"]["status"] == "pass"
    assert readiness["gates"]["public_baseline_native_metric_template"]["status"] == "pass"
    assert readiness["gates"]["native_public_jepa_benchmark"]["status"] == "pass"
    assert readiness["gates"]["artifact_review_bundle"]["status"] == "pass"
    if readiness["gates"]["public_minigrid_execution"]["status"] == "pass":
        assert "public_minigrid_execution" not in readiness["blocking_gates"]
    else:
        assert "public_minigrid_execution" in readiness["blocking_gates"]
    assert "public_jepa_checkpoint_evaluation" not in readiness["blocking_gates"]
    assert "vjepa2_ac_minigrid_latent_prediction" not in readiness["blocking_gates"]
    assert "vjepa2_ac_near_native_reproduction" not in readiness["blocking_gates"]
    assert "public_minigrid_calibration_pareto" not in readiness["blocking_gates"]
    assert "public_minigrid_calibration_extension" not in readiness["blocking_gates"]
    assert "public_baseline_native_metric_contract" not in readiness["blocking_gates"]
    assert "public_baseline_native_metric_template" not in readiness["blocking_gates"]
    assert "native_public_jepa_benchmark" not in readiness["blocking_gates"]
    assert "artifact_review_bundle" not in readiness["blocking_gates"]
    assert readiness["blocking_gates"] == []
    assert readiness["evidence_boundary"] == {
        "checkpoint_evaluation": "closed",
        "vjepa2_ac_minigrid_latent_prediction": "closed",
        "vjepa2_ac_near_native_reproduction": "closed",
        "native_public_benchmark": "closed",
        "public_minigrid_calibration_pareto": "closed",
        "public_minigrid_calibration_extension": "closed",
        "public_baseline_native_metric_contract": "closed",
        "public_baseline_native_metric_template": "closed",
        "artifact_review_bundle": "closed",
    }
    remaining = readiness["remaining_evidence_contracts"]
    retraining = remaining["true_retraining_loss_ablation"]
    native = remaining["vjepa2_ac_native_reproduction"]
    assert retraining["status"] == "closed"
    assert retraining["executed_rows"] == [
        "full_s3",
        "minus_l_gap",
        "minus_l_intervention",
        "minus_l_stab",
        "minus_l_unlogged",
    ]
    assert retraining["source_debt_rows"] == []
    assert "stability_consistency" in retraining["supervision_surface_contract"]
    assert "intervention_bce" in retraining["supervision_surface_contract"]
    assert native["status"] == "not_evaluated"
    assert native["near_native_record_status"] == "evaluated_near_native"
    assert native["near_native_record"] == "reports/bedc_vjepa2_ac_native_reproduction.json"
    assert native["native_metric_contract_status"] == "contract_ready"
    assert native["native_metric_contract"] == "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    assert native["native_metric_template_status"] == "recorded"
    assert native["native_metric_template"] == "reports/bedc_jepa_public_baseline_native_metric_template.json"
    assert "native_acceptance_contract" in native
    assert "required_native_evidence" in native["native_acceptance_contract"]
    assert (
        "execute the recorded public baseline native metric contract on an official or external benchmark stream"
        in readiness["next_actions"]
    )
    assert (
        "extend public MiniGrid calibration beyond the current symbolic-control readback scope"
        in readiness["next_actions"]
    )
    assert (
        "import a public pixel-world benchmark result satisfying the recorded scope contract"
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
