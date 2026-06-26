from scripts.build_bedc_jepa_artifact_manifest import build_manifest
from scripts.run_bedc_jepa_experiment import run_experiment


def test_bedc_jepa_artifact_manifest_records_evidence_ready_claims():
    manifest = build_manifest(run_experiment())

    assert manifest["schema_id"] == "bedc-jepa-artifact-manifest"
    assert manifest["artifact"] == "reports/bedc_jepa_four_system_experiment.json"
    assert manifest["commands"]["generate"] == "python scripts/run_bedc_jepa_experiment.py"
    assert manifest["commands"]["torch_objective"] == "python scripts/run_torch_bedc_jepa.py"
    assert (
        manifest["commands"]["torch_retraining_loss_ablation"]
        == "python scripts/run_torch_retraining_loss_ablation.py"
    )
    assert manifest["commands"]["public_minigrid_probe"] == "python scripts/probe_public_minigrid.py"
    assert (
        manifest["commands"]["public_minigrid_native_benchmark"]
        == "python scripts/run_public_minigrid_native_benchmark.py"
    )
    assert (
        manifest["commands"]["public_minigrid_native_seed_sweep"]
        == "python scripts/run_public_minigrid_native_seed_sweep.py"
    )
    assert (
        manifest["commands"]["public_minigrid_debt_closure"]
        == "python scripts/build_public_minigrid_debt_closure.py"
    )
    assert (
        manifest["commands"]["public_minigrid_calibration_extension"]
        == "python scripts/build_public_minigrid_calibration_extension.py"
    )
    assert (
        manifest["commands"]["public_benchmark_scope_contracts"]
        == "python scripts/build_public_benchmark_scope_contracts.py"
    )
    assert (
        manifest["commands"]["vjepa2_ac_native_boundary"]
        == "python scripts/build_vjepa2_ac_native_boundary.py"
    )
    assert (
        manifest["commands"]["latent_claim_certificate"]
        == "python scripts/run_bedc_latent_claim_certificate.py"
    )
    assert (
        manifest["commands"]["vjepa2_ac_minigrid_claim_certificate"]
        == "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py"
    )
    assert (
        manifest["commands"]["vjepa2_ac_minigrid_latent_prediction"]
        == "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py"
    )
    assert (
        manifest["commands"]["vjepa2_ac_near_native_reproduction"]
        == "python scripts/build_vjepa2_ac_near_native_reproduction.py"
    )
    assert (
        manifest["commands"]["import_public_minigrid_benchmark_metrics"]
        == "python scripts/import_public_minigrid_benchmark_metrics.py <minigrid-result.json>"
    )
    assert (
        manifest["commands"]["export_public_minigrid_benchmark_result"]
        == "python scripts/export_public_minigrid_benchmark_result.py"
    )
    assert (
        manifest["commands"]["public_jepa_baseline_registry"]
        == "python scripts/build_public_jepa_baseline_registry.py"
    )
    assert (
        manifest["commands"]["public_baseline_native_metric_contract"]
        == "python scripts/build_public_baseline_native_metric_contract.py"
    )
    assert (
        manifest["commands"]["public_baseline_native_metric_template"]
        == "python scripts/build_public_baseline_native_metric_template.py"
    )
    assert (
        manifest["commands"]["probe_public_jepa_baseline"]
        == "python scripts/probe_public_jepa_baseline.py"
    )
    assert (
        manifest["commands"]["run_public_jepa_structure_adapter"]
        == "python scripts/run_public_jepa_structure_adapter.py"
    )
    assert (
        manifest["commands"]["build_public_jepa_adapter_comparison"]
        == "python scripts/build_public_jepa_adapter_comparison.py"
    )
    assert (
        manifest["commands"]["run_public_jepa_ac_giant_adapter"]
        == "python scripts/run_public_jepa_ac_giant_adapter.py"
    )
    assert (
        manifest["commands"]["build_public_jepa_cuda_comparison"]
        == "python scripts/build_public_jepa_cuda_comparison.py"
    )
    assert (
        manifest["commands"]["import_public_jepa_baseline_metrics"]
        == "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>"
    )
    assert (
        manifest["commands"]["export_public_jepa_baseline_result"]
        == "python scripts/export_public_jepa_baseline_result.py"
    )
    assert manifest["commands"]["external_run_kit"] == "python scripts/build_bedc_jepa_external_run_kit.py"
    assert manifest["commands"]["review_bundle"] == "python scripts/build_bedc_jepa_review_bundle.py"
    assert (
        manifest["commands"]["quality_backend_candidate"]
        == "python scripts/build_bedc_jepa_quality_backend_candidate.py"
    )
    assert manifest["commands"]["quality_lab_export"] == "python scripts/build_bedc_jepa_quality_lab_export.py"
    assert (
        manifest["commands"]["paper_writeback_packet"]
        == "python scripts/build_bedc_jepa_paper_writeback_packet.py"
    )
    assert manifest["commands"]["readiness"] == "python scripts/build_bedc_jepa_readiness.py"
    assert manifest["commands"]["test"] == "python -m pytest -q"
    assert (
        manifest["objective_artifacts"]["boundary_envelope"]
        == "reports/bedc_jepa_boundary_envelope.json"
    )
    assert manifest["objective_artifacts"]["torch"] == "reports/bedc_jepa_torch_objective.json"
    assert (
        manifest["objective_artifacts"]["torch_retraining_loss_ablation"]
        == "reports/bedc_jepa_retraining_loss_ablation.json"
    )
    assert manifest["readiness"] == "reports/bedc_jepa_readiness.json"
    assert manifest["external_run_kit"] == "reports/bedc_jepa_external_run_kit.json"
    assert manifest["review_bundle"] == "reports/bedc_jepa_review_bundle.json"
    assert manifest["quality_backend_candidate"] == "reports/bedc_jepa_quality_backend_candidate.json"
    assert manifest["quality_lab_export"] == "reports/bedc_jepa_quality_lab_exports.json"
    assert manifest["paper_writeback_packet"] == "reports/bedc_jepa_paper_writeback_packet.json"
    assert (
        manifest["latent_claim_certificates"]["certificates"]
        == "reports/bedc_latent_claim_certificates.json"
    )
    assert (
        manifest["latent_claim_certificates"]["conformal_gap_sweep"]
        == "reports/bedc_conformal_gap_sweep.json"
    )
    assert (
        manifest["latent_claim_certificates"]["claim_boundary_audit"]
        == "reports/bedc_claim_boundary_audit.json"
    )
    assert (
        manifest["latent_claim_certificates"]["vjepa2_ac_minigrid_claim_certificate"]
        == "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json"
    )
    assert manifest["public_baselines"]["jepa_comparison"] == "reports/bedc_jepa_public_baseline_comparison.json"
    assert manifest["public_baselines"]["public_benchmark_scope_contracts"] == (
        "reports/bedc_jepa_public_benchmark_scope_contracts.json"
    )
    assert manifest["public_baselines"]["jepa_native_metric_contract"] == (
        "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert manifest["public_baselines"]["jepa_native_metric_template"] == (
        "reports/bedc_jepa_public_baseline_native_metric_template.json"
    )
    assert (
        manifest["public_baselines"]["jepa_ac_native_boundary"]
        == "reports/bedc_jepa_vjepa2_ac_native_boundary.json"
    )
    assert (
        manifest["public_baselines"]["jepa_ac_giant_adapter"]
        == "reports/bedc_jepa_public_ac_giant_adapter.json"
    )
    assert (
        manifest["public_baselines"]["jepa_ac_minigrid_latent_prediction"]
        == "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json"
    )
    assert (
        manifest["public_baselines"]["jepa_ac_near_native_reproduction"]
        == "reports/bedc_vjepa2_ac_native_reproduction.json"
    )
    assert (
        manifest["public_baselines"]["jepa_ac_near_native_readback_comparison"]
        == "reports/bedc_vjepa2_ac_native_readback_comparison.json"
    )
    assert (
        manifest["public_baselines"]["jepa_cuda_adapter_comparison"]
        == "reports/bedc_jepa_public_cuda_adapter_comparison.json"
    )
    assert (
        manifest["public_baselines"]["jepa_public_adapter_comparison"]
        == "reports/bedc_jepa_public_adapter_comparison.json"
    )
    assert (
        manifest["public_baselines"]["jepa_public_structure_adapter"]
        == "reports/bedc_jepa_public_structure_adapter.json"
    )
    assert (
        manifest["public_baselines"]["jepa_public_pretrained_vitb_adapter"]
        == "reports/bedc_jepa_public_pretrained_vitb_adapter.json"
    )
    assert manifest["public_baselines"]["jepa_registry"] == "reports/bedc_jepa_public_baseline_registry.json"
    assert (
        manifest["public_baselines"]["jepa_probe"]
        == "reports/bedc_jepa_public_baseline_probe.json"
    )
    assert (
        manifest["public_baselines"]["jepa_external_result"]
        == "reports/bedc_jepa_public_baseline_external_result.json"
    )
    assert manifest["public_adapters"]["minigrid"] == "reports/bedc_jepa_public_minigrid_probe.json"
    assert (
        manifest["public_adapters"]["minigrid_benchmark_packet"]
        == "reports/bedc_jepa_public_minigrid_benchmark_packet.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_native_benchmark"]
        == "reports/bedc_jepa_public_native_minigrid_benchmark.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_native_seed_sweep"]
        == "reports/bedc_jepa_public_native_minigrid_seed_sweep.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_public_debt_decomposition"]
        == "reports/bedc_jepa_public_debt_decomposition.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_conformal_certified_coverage"]
        == "reports/bedc_jepa_conformal_certified_coverage.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_risk_success_pareto"]
        == "reports/bedc_jepa_risk_success_pareto.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_calibration_extension"]
        == "reports/bedc_jepa_public_minigrid_calibration_extension.json"
    )
    assert manifest["public_adapters"]["minigrid_loss_ablation"] == "reports/bedc_jepa_loss_ablation.json"
    assert (
        manifest["public_adapters"]["minigrid_external_result"]
        == "reports/bedc_jepa_public_minigrid_external_result.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_transition_packet"]
        == "reports/bedc_jepa_public_minigrid_transition_packet.json"
    )

    assert "contact_ready_claims" not in manifest
    claims = manifest["evidence_ready_claims"]
    assert claims["four_system_ablation"] == ["S0", "S1", "S2", "S3"]
    assert claims["grid_transition_one_step_r2"] > 0.90
    assert claims["minigrid_transition_one_step_accuracy"] > 0.94
    assert claims["minigrid_gap_auc_gain"] > 0.40
    assert claims["minigrid_risk_adjusted_planning_gain"] > 0.0
    assert claims["object_intervention_counterfactual_accuracy_mean"] > 0.90
    assert claims["multi_object_counterfactual_accuracy_mean"] > 0.88
    assert claims["cluttered_object_counterfactual_accuracy_mean"] > 0.86
    assert claims["cluttered_object_gap_auc_gain_mean"] > 0.40
    assert claims["cluttered_object_unlogged_error_reduction_mean"] > 0.20

    assert "native public JEPA benchmark comparison" in manifest["cannot_claim"]
    assert "public benchmark superiority" in manifest["cannot_claim"]
    assert "general autonomous intelligence" in manifest["cannot_claim"]
