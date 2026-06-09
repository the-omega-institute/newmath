from bedc_quality_lab.bedc_jepa_external_run_kit import build_external_run_kit


def test_external_run_kit_records_result_schemas_and_gate_conditions():
    kit = build_external_run_kit()

    assert kit["schema_id"] == "bedc-jepa-external-run-kit"
    assert kit["status"] == "review_ready"
    assert set(kit["required_external_results"]) == {
        "public_jepa_checkpoint_evaluation",
        "public_minigrid_execution",
        "public_jepa_baseline",
        "torch_retraining_loss_ablation",
        "vjepa2_ac_native_reproduction",
        "vjepa2_ac_minigrid_claim_certificate",
        "vjepa2_ac_minigrid_latent_prediction",
    }
    checkpoint = kit["required_external_results"]["public_jepa_checkpoint_evaluation"]
    minigrid = kit["required_external_results"]["public_minigrid_execution"]
    baseline = kit["required_external_results"]["public_jepa_baseline"]
    retraining = kit["required_external_results"]["torch_retraining_loss_ablation"]
    native_reproduction = kit["required_external_results"]["vjepa2_ac_native_reproduction"]
    vjepa_lccp = kit["required_external_results"]["vjepa2_ac_minigrid_claim_certificate"]
    vjepa_latent = kit["required_external_results"]["vjepa2_ac_minigrid_latent_prediction"]

    assert checkpoint["readiness_gate"] == "public_jepa_checkpoint_evaluation"
    assert checkpoint["run_command"] == "python scripts/run_public_jepa_ac_giant_adapter.py"
    assert checkpoint["comparison_command"] == "python scripts/build_public_jepa_cuda_comparison.py"
    assert "checkpoint_status is loaded" in checkpoint["pass_condition"]
    assert minigrid["import_command"] == "python scripts/import_public_minigrid_benchmark_metrics.py <minigrid-result.json>"
    assert baseline["target_artifact"] == "reports/bedc_jepa_public_native_minigrid_benchmark.json"
    assert baseline["run_command"] == "python scripts/run_public_minigrid_native_benchmark.py"
    assert baseline["seed_sweep_command"] == "python scripts/run_public_minigrid_native_seed_sweep.py"
    assert baseline["import_command"] == "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>"
    assert "gap_detection_auc" in minigrid["required_fields"]
    assert "jepa_family_baseline_boundary" in baseline["required_fields"]
    assert minigrid["readiness_gate"] == "public_minigrid_execution"
    assert baseline["readiness_gate"] == "native_public_jepa_benchmark"
    assert retraining["readiness_gate"] == "full_retraining_loss_ablation"
    assert retraining["target_artifact"] == "reports/bedc_jepa_retraining_loss_ablation.json"
    assert retraining["run_command"] == "python scripts/run_torch_retraining_loss_ablation.py"
    assert "minus_l_unlogged" in retraining["required_systems"]
    assert "minus_l_gap" in retraining["required_systems"]
    assert "minus_l_stab" in retraining["required_systems"]
    assert "minus_l_intervention" in retraining["required_systems"]
    assert "stability_source_split" in retraining["source_surface_contract"]["stability_consistency"]
    assert (
        "intervention_source_split"
        in retraining["source_surface_contract"]["intervention_bce"]
    )
    assert "true retraining rows" in retraining["pass_condition"]
    assert native_reproduction["readiness_gate"] == "vjepa2_ac_native_reproduction"
    assert native_reproduction["target_artifact"] == "reports/bedc_vjepa2_ac_native_reproduction.json"
    assert native_reproduction["boundary_record"] == "reports/bedc_jepa_vjepa2_ac_native_boundary.json"
    assert "native_or_near_native_rollout_score" in native_reproduction["required_fields"]
    assert "bedc_readback_metrics" in native_reproduction["required_fields"]
    assert "same_train_cal_test_split" in native_reproduction["parity_protocol_fields"]
    assert "same_bedc_predicate_set" in native_reproduction["parity_protocol_fields"]
    assert "remains unevaluated" in native_reproduction["pass_condition"]
    assert vjepa_lccp["readiness_gate"] == "vjepa2_ac_fixed_carrier_lccp"
    assert vjepa_lccp["target_artifact"] == "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json"
    assert vjepa_lccp["run_command"] == "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py"
    assert "execution_contract" in vjepa_lccp["required_fields"]
    assert "checkpoint_contract" in vjepa_lccp["required_fields"]
    assert "feature_contract" in vjepa_lccp["required_fields"]
    assert "door_key_context_visible" in vjepa_lccp["required_predicates"]
    assert "source-debt status under LCCP" in vjepa_lccp["pass_condition"]
    assert vjepa_latent["target_artifact"] == "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json"
    assert vjepa_latent["run_command"] == "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py"
    assert "execution_contract" in vjepa_latent["required_fields"]
    assert "checkpoint_contract" in vjepa_latent["required_fields"]
    assert "feature_contract" in vjepa_latent["required_fields"]
    assert "metrics" in vjepa_latent["required_fields"]
    assert "feature, and cannot-claim contracts" in vjepa_latent["pass_condition"]
    assert kit["readiness_command"] == "python scripts/build_bedc_jepa_readiness.py"
    assert kit["review_bundle_command"] == "python scripts/build_bedc_jepa_review_bundle.py"
    assert (
        kit["quality_backend_candidate_command"]
        == "python scripts/build_bedc_jepa_quality_backend_candidate.py"
    )
    assert (
        kit["latent_claim_certificate_command"]
        == "python scripts/run_bedc_latent_claim_certificate.py"
    )
    assert (
        kit["torch_retraining_loss_ablation_command"]
        == "python scripts/run_torch_retraining_loss_ablation.py"
    )
    assert (
        kit["vjepa2_ac_minigrid_claim_certificate_command"]
        == "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py"
    )
    assert (
        kit["vjepa2_ac_minigrid_latent_prediction_command"]
        == "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py"
    )
    assert (
        minigrid["export_command"]
        == "python scripts/export_public_minigrid_benchmark_result.py"
    )
    assert (
        baseline["export_command"]
        == "python scripts/export_public_jepa_baseline_result.py"
    )
    assert (
        baseline["probe_command"]
        == "python scripts/probe_public_jepa_baseline.py"
    )
