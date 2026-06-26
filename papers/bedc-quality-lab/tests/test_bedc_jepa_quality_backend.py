from bedc_quality_lab.bedc_jepa_quality_backend import (
    BACKEND_NAME,
    LOADER_PATH,
    METRICS,
    NOT_CLAIMED,
    SCHEMA_ID,
    build_quality_backend_candidate,
)


def test_quality_backend_candidate_exposes_bounded_adapter_contract():
    packet = build_quality_backend_candidate()

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["backend"]["name"] == BACKEND_NAME
    assert packet["backend"]["scope_kind"] == "non-canonical-backend-probe"
    assert packet["backend"]["candidate_loader_path"] == LOADER_PATH
    assert packet["backend"]["metrics"] == list(METRICS)
    assert packet["backend"]["not_claimed"] == list(NOT_CLAIMED)
    assert packet["source_spec"]["world_state_contract"] == (
        "continuous latent state plus operational distinctions plus gap ledger"
    )
    assert packet["classifier_spec"]["adapter_boundary"] == "thin projection over existing BEDC-JEPA reports"
    assert packet["forbidden_surfaces"] == [
        "model runner execution",
        "canonical writer execution",
        "terminal verdict projection",
        "raw benchmark regeneration",
    ]


def test_quality_backend_metrics_are_projection_cells_only():
    packet = build_quality_backend_candidate()
    metrics = packet["metrics"]

    assert tuple(metrics) == METRICS
    assert metrics["torch_objective_gap_auc_gain_mean"] > 0.20
    assert metrics["torch_objective_debt_reduction_mean"] > 0.05
    assert metrics["torch_objective_latent_r2_delta_abs_max"] == 0.0
    assert metrics["minigrid_gap_auc_gain"] > 0.40
    assert metrics["native_unlogged_error_reduction"] > 0.05
    assert metrics["native_planning_high_gap_reduction"] > 0.05
    assert metrics["checkpoint_evaluation_closed"] == 1.0
    assert metrics["native_public_benchmark_closed"] == 1.0
    assert metrics["public_minigrid_calibration_pareto_closed"] == 1.0
    assert metrics["public_minigrid_calibration_extension_closed"] == 1.0
    assert metrics["public_minigrid_calibration_row_count"] == 75.0
    assert metrics["public_minigrid_calibration_executed_row_count"] == 75.0
    assert metrics["public_minigrid_calibration_source_gap_row_count"] == 0.0
    assert metrics["public_minigrid_calibration_risk_reduction_mean"] > 0.0
    assert 0.0 <= metrics["public_minigrid_calibration_total_debt_direction_win_rate"] <= 1.0
    assert metrics["artifact_review_bundle_closed"] == 1.0
    assert metrics["retraining_ablation_recorded"] in {0.0, 1.0}
    assert metrics["retraining_ablation_recorded"] == 1.0
    assert metrics["full_retraining_loss_ablation_closed"] == 1.0
    assert metrics["vjepa2_ac_lccp_recorded"] in {0.0, 1.0}
    assert metrics["vjepa2_ac_latent_prediction_score"] >= 0.0
    assert metrics["vjepa2_ac_near_native_recorded"] == 1.0
    assert metrics["public_baseline_native_metric_contract_recorded"] == 1.0
    assert metrics["public_baseline_native_metric_template_recorded"] == 1.0
    assert metrics["vjepa2_ac_official_reproduction_evaluated"] == 0.0
    assert "terminal_verdict" not in metrics
    assert "raw_records" not in packet


def test_quality_backend_ledger_rows_pin_claim_boundaries():
    packet = build_quality_backend_candidate()
    rows = {row["key"]: row for row in packet["ledger_rows"]}

    assert rows["source/operational-distinction-grounding"]["status"] == "closed"
    assert rows["source/gap-ledger-label-grounding"]["status"] == "closed"
    assert rows["classifier/distinction-head-certificate"]["status"] == "closed"
    assert rows["classifier/gap-head-certificate"]["status"] == "closed"
    assert rows["stability/public-benchmark-evidence-readiness"]["status"] == "closed"
    assert rows["calibration/public-minigrid-calibration-pareto"]["status"] == "closed"
    assert rows["calibration/public-minigrid-calibration-extension"]["status"] == "closed"
    assert rows["generalization/global-claim-boundary"]["status"] == "closed"
    assert rows["mechanism/mechanism-closure-debt"]["status"] == "open"
    assert rows["mechanism/mechanism-closure-debt"]["severity"] == "boundary"
    assert rows["mechanism/full-retraining-loss-ablation"]["status"] == "closed"
    assert rows["mechanism/full-retraining-loss-ablation"]["evidence_pointer"] == (
        "reports/bedc_jepa_review_bundle.json:$.remaining_evidence_contracts.true_retraining_loss_ablation"
    )
    assert rows["classifier/vjepa2-ac-fixed-carrier-lccp"]["status"] in {"open", "closed"}
    assert rows["mechanism/vjepa2-ac-minigrid-latent-prediction"]["status"] in {"open", "closed"}
    assert rows["mechanism/vjepa2-ac-near-native-minigrid-record"]["status"] == "closed"
    assert rows["mechanism/public-baseline-native-metric-contract"]["status"] == "closed"
    assert rows["mechanism/public-baseline-native-metric-contract"]["evidence_pointer"] == (
        "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert rows["mechanism/public-baseline-native-metric-template"]["status"] == "closed"
    assert rows["mechanism/public-baseline-native-metric-template"]["evidence_pointer"] == (
        "reports/bedc_jepa_public_baseline_native_metric_template.json"
    )
    assert all(row["owner"] == "bedc_quality_lab.bedc_jepa_quality_backend.build_quality_backend_candidate" for row in rows.values())
    assert "large-scale real-world conclusion" in packet["not_claimed"]
    assert "mechanism closure" in packet["not_claimed"]


def test_quality_backend_projects_remaining_evidence_contracts():
    packet = build_quality_backend_candidate()
    remaining = packet["remaining_evidence_contracts"]

    assert remaining["true_retraining_loss_ablation"]["status"] == "closed"
    assert remaining["true_retraining_loss_ablation"]["source_debt_rows"] == []
    assert "stability_consistency" in remaining["true_retraining_loss_ablation"]["supervision_surface_contract"]
    assert "intervention_bce" in remaining["true_retraining_loss_ablation"]["supervision_surface_contract"]
    assert remaining["vjepa2_ac_native_reproduction"]["status"] == "not_evaluated"
    assert remaining["vjepa2_ac_native_reproduction"]["near_native_record_status"] == "evaluated_near_native"
    assert (
        "native_acceptance_contract"
        in remaining["vjepa2_ac_native_reproduction"]
    )
    assert (
        remaining["vjepa2_ac_native_reproduction"]["native_metric_contract"]
        == "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )


def test_quality_backend_artifacts_are_existing_report_pointers():
    packet = build_quality_backend_candidate()

    assert packet["artifacts"]["artifact_manifest"] == "reports/bedc_jepa_artifact_manifest.json"
    assert packet["artifacts"]["readiness"] == "reports/bedc_jepa_readiness.json"
    assert packet["artifacts"]["review_bundle"] == "reports/bedc_jepa_review_bundle.json"
    assert packet["artifacts"]["native_minigrid"] == "reports/bedc_jepa_public_native_minigrid_benchmark.json"
    assert packet["artifacts"]["latent_claim_certificates"] == "reports/bedc_latent_claim_certificates.json"
    assert packet["artifacts"]["conformal_gap_sweep"] == "reports/bedc_conformal_gap_sweep.json"
    assert packet["artifacts"]["claim_boundary_audit"] == "reports/bedc_claim_boundary_audit.json"
    assert (
        packet["artifacts"]["public_minigrid_calibration_extension"]
        == "reports/bedc_jepa_public_minigrid_calibration_extension.json"
    )
    assert packet["artifacts"]["retraining_loss_ablation"] == "reports/bedc_jepa_retraining_loss_ablation.json"
    assert (
        packet["artifacts"]["vjepa2_ac_minigrid_claim_certificate"]
        == "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json"
    )
    assert (
        packet["artifacts"]["vjepa2_ac_minigrid_latent_prediction"]
        == "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json"
    )
    assert (
        packet["artifacts"]["vjepa2_ac_near_native_reproduction"]
        == "reports/bedc_vjepa2_ac_native_reproduction.json"
    )
    assert (
        packet["artifacts"]["vjepa2_ac_native_readback_comparison"]
        == "reports/bedc_vjepa2_ac_native_readback_comparison.json"
    )
    assert (
        packet["artifacts"]["public_baseline_native_metric_contract"]
        == "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert (
        packet["artifacts"]["public_baseline_native_metric_template"]
        == "reports/bedc_jepa_public_baseline_native_metric_template.json"
    )
    assert (
        packet["artifacts"]["public_benchmark_scope_contracts"]
        == "reports/bedc_jepa_public_benchmark_scope_contracts.json"
    )
