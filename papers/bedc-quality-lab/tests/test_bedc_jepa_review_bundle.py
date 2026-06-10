from bedc_quality_lab.bedc_jepa_review_bundle import build_review_bundle


def test_review_bundle_records_reproducibility_contract_and_boundaries():
    bundle = build_review_bundle()

    assert bundle["schema_id"] == "bedc-jepa-review-bundle"
    assert bundle["status"] in {"review_ready", "incomplete"}
    assert bundle["source_commit_at_build"] == bundle["source_commit_observed_at_build"]
    assert "not a self-referential assertion" in bundle["source_commit_semantics"]
    assert bundle["required_artifacts"]["readiness"] == "reports/bedc_jepa_readiness.json"
    assert bundle["required_artifacts"]["boundary_envelope"] == "reports/bedc_jepa_boundary_envelope.json"
    assert bundle["required_artifacts"]["native_minigrid_seed_sweep"] == (
        "reports/bedc_jepa_public_native_minigrid_seed_sweep.json"
    )
    assert bundle["required_artifacts"]["public_debt_decomposition"] == (
        "reports/bedc_jepa_public_debt_decomposition.json"
    )
    assert bundle["required_artifacts"]["conformal_certified_coverage"] == (
        "reports/bedc_jepa_conformal_certified_coverage.json"
    )
    assert bundle["required_artifacts"]["risk_success_pareto"] == "reports/bedc_jepa_risk_success_pareto.json"
    assert bundle["required_artifacts"]["public_minigrid_calibration_extension"] == (
        "reports/bedc_jepa_public_minigrid_calibration_extension.json"
    )
    assert bundle["required_artifacts"]["loss_ablation"] == "reports/bedc_jepa_loss_ablation.json"
    assert bundle["required_artifacts"]["retraining_loss_ablation"] == (
        "reports/bedc_jepa_retraining_loss_ablation.json"
    )
    assert bundle["required_artifacts"]["public_baseline_native_metric_contract"] == (
        "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert bundle["required_artifacts"]["public_baseline_native_metric_template"] == (
        "reports/bedc_jepa_public_baseline_native_metric_template.json"
    )
    assert bundle["required_artifacts"]["public_benchmark_scope_contracts"] == (
        "reports/bedc_jepa_public_benchmark_scope_contracts.json"
    )
    assert bundle["required_artifacts"]["public_adapter_comparison"] == (
        "reports/bedc_jepa_public_adapter_comparison.json"
    )
    assert bundle["required_artifacts"]["public_structure_adapter"] == (
        "reports/bedc_jepa_public_structure_adapter.json"
    )
    assert bundle["required_artifacts"]["public_pretrained_vitb_adapter"] == (
        "reports/bedc_jepa_public_pretrained_vitb_adapter.json"
    )
    assert bundle["required_artifacts"]["quality_backend_candidate"] == (
        "reports/bedc_jepa_quality_backend_candidate.json"
    )
    assert bundle["required_artifacts"]["quality_lab_export"] == "reports/bedc_jepa_quality_lab_exports.json"
    assert bundle["required_artifacts"]["paper_writeback_packet"] == (
        "reports/bedc_jepa_paper_writeback_packet.json"
    )
    assert bundle["required_artifacts"]["latent_claim_certificates"] == (
        "reports/bedc_latent_claim_certificates.json"
    )
    assert bundle["required_artifacts"]["conformal_gap_sweep"] == (
        "reports/bedc_conformal_gap_sweep.json"
    )
    assert bundle["required_artifacts"]["claim_boundary_audit"] == (
        "reports/bedc_claim_boundary_audit.json"
    )
    assert bundle["required_artifacts"]["vjepa2_ac_minigrid_claim_certificate"] == (
        "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json"
    )
    assert bundle["required_artifacts"]["vjepa2_ac_minigrid_latent_prediction"] == (
        "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json"
    )
    assert bundle["required_artifacts"]["vjepa2_ac_near_native_reproduction"] == (
        "reports/bedc_vjepa2_ac_native_reproduction.json"
    )
    assert bundle["required_artifacts"]["vjepa2_ac_native_readback_comparison"] == (
        "reports/bedc_vjepa2_ac_native_readback_comparison.json"
    )
    assert "python scripts/run_public_minigrid_native_seed_sweep.py" in bundle["reproduction_commands"]
    assert "python scripts/build_public_minigrid_debt_closure.py" in bundle["reproduction_commands"]
    assert "python scripts/build_public_minigrid_calibration_extension.py" in bundle["reproduction_commands"]
    assert "python scripts/run_torch_retraining_loss_ablation.py" in bundle["reproduction_commands"]
    assert "python scripts/build_public_baseline_native_metric_contract.py" in bundle["reproduction_commands"]
    assert "python scripts/build_public_baseline_native_metric_template.py" in bundle["reproduction_commands"]
    assert "python scripts/build_public_benchmark_scope_contracts.py" in bundle["reproduction_commands"]
    assert "python scripts/run_public_jepa_structure_adapter.py" in bundle["reproduction_commands"]
    assert "python scripts/build_public_jepa_adapter_comparison.py" in bundle["reproduction_commands"]
    assert "python scripts/build_bedc_jepa_quality_backend_candidate.py" in bundle["reproduction_commands"]
    assert "python scripts/build_bedc_jepa_quality_lab_export.py" in bundle["reproduction_commands"]
    assert "python scripts/build_bedc_jepa_paper_writeback_packet.py" in bundle["reproduction_commands"]
    assert "python scripts/run_bedc_latent_claim_certificate.py" in bundle["reproduction_commands"]
    assert "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py" in bundle["reproduction_commands"]
    assert "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py" in bundle["reproduction_commands"]
    assert "python scripts/build_vjepa2_ac_near_native_reproduction.py" in bundle["reproduction_commands"]
    assert "pdflatex -interaction=nonstopmode -halt-on-error main.tex" in bundle["reproduction_commands"]
    assert bundle["checks"]["checkpoint_evaluation"] == "closed"
    assert bundle["checks"]["native_public_benchmark"] == "closed"
    assert bundle["checks"]["native_unlogged_error_reduction"] > 0.05
    assert bundle["checks"]["native_planning_high_gap_reduction"] > 0.05
    assert bundle["checks"]["public_debt_diagnosis"] == "silent debt falls while coverage debt rises"
    assert bundle["checks"]["public_conformal_predicate_count"] >= 5.0
    assert bundle["checks"]["public_minigrid_calibration_extension_status"] in {"executed", "not recorded"}
    assert bundle["checks"]["public_minigrid_calibration_extension_executed_rows"] >= 0.0
    assert 0.0 <= bundle["checks"]["public_minigrid_calibration_extension_silent_win_rate"] <= 1.0
    assert 0.0 <= bundle["checks"]["public_minigrid_calibration_extension_risk_win_rate"] <= 1.0
    assert bundle["checks"]["public_ablation_unlogged_penalty_effect"] >= 0.0
    assert bundle["checks"]["retraining_ablation_system_count"] >= 0.0
    assert bundle["checks"]["public_baseline_native_metric_contract_status"] in {
        "contract_ready",
        "not recorded",
    }
    assert bundle["checks"]["public_baseline_native_metric_required_field_count"] >= 0.0
    assert bundle["checks"]["public_baseline_native_metric_template_status"] in {
        "recorded",
        "not recorded",
    }
    assert bundle["checks"]["public_benchmark_scope_contract_status"] in {
        "contract_ready",
        "not recorded",
    }
    assert bundle["checks"]["public_benchmark_scope_contract_count"] >= 0.0
    assert bundle["checks"]["public_adapter_comparison_status"] in {"executed", "not recorded"}
    assert bundle["checks"]["public_structure_adapter_status"] in {"available", "not recorded"}
    assert bundle["checks"]["public_pretrained_vitb_adapter_status"] in {"available", "not recorded"}
    assert bundle["checks"]["quality_lab_export_status"] in {"recorded", "not recorded"}
    assert bundle["checks"]["quality_lab_export_count"] >= 0.0
    assert bundle["checks"]["paper_writeback_packet_status"] in {"paper_ready", "partial", "not recorded"}
    assert bundle["checks"]["paper_writeback_admitted_name"] in {"door_key_context_visible", "not recorded"}
    assert bundle["checks"]["vjepa2_ac_lccp_claim_count"] >= 0.0
    assert bundle["checks"]["vjepa2_ac_latent_prediction_score"] >= 0.0
    assert bundle["checks"]["vjepa2_ac_near_native_status"] in {"evaluated_near_native", "not recorded"}
    assert bundle["checks"]["vjepa2_ac_official_native_reproduction_status"] in {
        "not_evaluated",
        "not recorded",
    }
    assert bundle["checks"]["vjepa2_ac_near_native_latent_prediction_score"] >= 0.0
    remaining = bundle["remaining_evidence_contracts"]
    assert remaining["true_retraining_loss_ablation"]["status"] == "closed"
    assert remaining["true_retraining_loss_ablation"]["source_debt_rows"] == []
    assert "stability_consistency" in remaining["true_retraining_loss_ablation"]["supervision_surface_contract"]
    assert "intervention_bce" in remaining["true_retraining_loss_ablation"]["supervision_surface_contract"]
    assert (
        "required_native_evidence"
        in remaining["vjepa2_ac_native_reproduction"]["native_acceptance_contract"]
    )
    assert remaining["vjepa2_ac_native_reproduction"]["near_native_record_status"] == "evaluated_near_native"
    assert (
        remaining["vjepa2_ac_native_reproduction"]["native_metric_contract"]
        == "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )

    if bundle["status"] == "review_ready":
        assert bundle["failures"] == []
        assert bundle["checks"]["seed_sweep_count"] >= 5.0
        assert bundle["checks"]["seed_sweep_unlogged_error_win_rate"] >= 0.6
    else:
        assert bundle["failures"]
