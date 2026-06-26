from bedc_quality_lab.bedc_jepa_external_run_kit import build_external_run_kit


def test_external_run_kit_records_result_schemas_and_gate_conditions():
    kit = build_external_run_kit()

    assert kit["schema_id"] == "bedc-jepa-external-run-kit"
    assert kit["status"] == "review_ready"
    assert set(kit["required_external_results"]) == {
        "public_jepa_checkpoint_evaluation",
        "public_minigrid_execution",
        "public_jepa_baseline",
        "public_baseline_native_metric_contract",
        "public_minigrid_calibration_extension",
        "public_benchmark_scope_contracts",
        "torch_retraining_loss_ablation",
        "vjepa2_ac_native_reproduction",
        "vjepa2_ac_minigrid_claim_certificate",
        "vjepa2_ac_minigrid_latent_prediction",
        "quality_lab_export",
        "paper_writeback_packet",
    }
    checkpoint = kit["required_external_results"]["public_jepa_checkpoint_evaluation"]
    minigrid = kit["required_external_results"]["public_minigrid_execution"]
    baseline = kit["required_external_results"]["public_jepa_baseline"]
    native_metric_contract = kit["required_external_results"]["public_baseline_native_metric_contract"]
    extension = kit["required_external_results"]["public_minigrid_calibration_extension"]
    benchmark_scope = kit["required_external_results"]["public_benchmark_scope_contracts"]
    retraining = kit["required_external_results"]["torch_retraining_loss_ablation"]
    native_reproduction = kit["required_external_results"]["vjepa2_ac_native_reproduction"]
    vjepa_lccp = kit["required_external_results"]["vjepa2_ac_minigrid_claim_certificate"]
    vjepa_latent = kit["required_external_results"]["vjepa2_ac_minigrid_latent_prediction"]
    quality_lab_export = kit["required_external_results"]["quality_lab_export"]
    paper_writeback = kit["required_external_results"]["paper_writeback_packet"]

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
    assert native_metric_contract["readiness_gate"] == "public_baseline_native_metric_contract"
    assert native_metric_contract["target_artifact"] == (
        "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert native_metric_contract["template_artifact"] == (
        "reports/bedc_jepa_public_baseline_native_metric_template.json"
    )
    assert native_metric_contract["build_command"] == "python scripts/build_public_baseline_native_metric_contract.py"
    assert (
        native_metric_contract["template_command"]
        == "python scripts/build_public_baseline_native_metric_template.py"
    )
    assert "repository_commit" in native_metric_contract["required_execution_fields"]
    assert "checkpoint_identity" in native_metric_contract["required_execution_fields"]
    assert "dataset_identity" in native_metric_contract["required_execution_fields"]
    assert "execution_command" in native_metric_contract["required_execution_fields"]
    assert "bedc_readback_metrics" in native_metric_contract["required_execution_fields"]
    assert "lccp_certificate_metrics" in native_metric_contract["required_execution_fields"]
    assert "result satisfying this contract is imported" in native_metric_contract["pass_condition"]
    assert extension["readiness_gate"] == "public_minigrid_calibration_extension"
    assert extension["target_artifact"] == "reports/bedc_jepa_public_minigrid_calibration_extension.json"
    assert extension["run_command"] == "python scripts/build_public_minigrid_calibration_extension.py"
    assert extension["coverage_requirements"] == {
        "minimum_executed_rows": 30,
        "minimum_seed_count": 5,
        "minimum_task_variant_count": 3,
        "minimum_planning_budget_count": 3,
    }
    assert "at least 30 public MiniGrid calibration rows" in extension["pass_condition"]
    assert benchmark_scope["readiness_gate"] == "public_benchmark_scope_contracts"
    assert benchmark_scope["target_artifact"] == "reports/bedc_jepa_public_benchmark_scope_contracts.json"
    assert benchmark_scope["build_command"] == "python scripts/build_public_benchmark_scope_contracts.py"
    assert benchmark_scope["required_contracts"] == [
        "public_pixel_world_benchmark",
        "public_object_interaction_benchmark",
    ]
    assert "source gaps" in benchmark_scope["pass_condition"]
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
    assert native_reproduction["boundary_command"] == "python scripts/build_vjepa2_ac_native_boundary.py"
    assert native_reproduction["run_command"] == "python scripts/build_vjepa2_ac_near_native_reproduction.py"
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
    assert quality_lab_export["readiness_gate"] == "quality_lab_export_registry"
    assert quality_lab_export["target_artifact"] == "reports/bedc_jepa_quality_lab_exports.json"
    assert quality_lab_export["build_command"] == "python scripts/build_bedc_jepa_quality_lab_export.py"
    assert "exports" in quality_lab_export["required_fields"]
    assert "rollup-style quality-lab export registry" in quality_lab_export["pass_condition"]
    assert paper_writeback["readiness_gate"] == "paper_writeback_packet"
    assert paper_writeback["target_artifact"] == "reports/bedc_jepa_paper_writeback_packet.json"
    assert paper_writeback["build_command"] == "python scripts/build_bedc_jepa_paper_writeback_packet.py"
    assert "record" in paper_writeback["required_fields"]
    assert "without adding empirical claims" in paper_writeback["pass_condition"]
    assert kit["readiness_command"] == "python scripts/build_bedc_jepa_readiness.py"
    assert kit["review_bundle_command"] == "python scripts/build_bedc_jepa_review_bundle.py"
    assert (
        kit["quality_backend_candidate_command"]
        == "python scripts/build_bedc_jepa_quality_backend_candidate.py"
    )
    assert kit["quality_lab_export_command"] == "python scripts/build_bedc_jepa_quality_lab_export.py"
    assert kit["paper_writeback_packet_command"] == "python scripts/build_bedc_jepa_paper_writeback_packet.py"
    assert (
        kit["latent_claim_certificate_command"]
        == "python scripts/run_bedc_latent_claim_certificate.py"
    )
    assert (
        kit["torch_retraining_loss_ablation_command"]
        == "python scripts/run_torch_retraining_loss_ablation.py"
    )
    assert kit["public_baseline_native_metric_contract_command"] == (
        "python scripts/build_public_baseline_native_metric_contract.py"
    )
    assert kit["public_baseline_native_metric_template_command"] == (
        "python scripts/build_public_baseline_native_metric_template.py"
    )
    assert (
        kit["public_minigrid_calibration_extension_command"]
        == "python scripts/build_public_minigrid_calibration_extension.py"
    )
    assert (
        kit["public_benchmark_scope_contracts_command"]
        == "python scripts/build_public_benchmark_scope_contracts.py"
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
        kit["vjepa2_ac_native_boundary_command"]
        == "python scripts/build_vjepa2_ac_native_boundary.py"
    )
    assert (
        kit["vjepa2_ac_near_native_reproduction_command"]
        == "python scripts/build_vjepa2_ac_near_native_reproduction.py"
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
