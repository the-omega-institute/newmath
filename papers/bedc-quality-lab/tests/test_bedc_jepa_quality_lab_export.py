from bedc_quality_lab.bedc_jepa_quality_lab_export import (
    OWNER,
    SCHEMA_ID,
    build_quality_lab_export,
)


def test_bedc_jepa_quality_lab_export_records_rollup_shape():
    payload = build_quality_lab_export()

    assert payload["schema_id"] == SCHEMA_ID
    assert payload["generated_at"] == "pipeline-generated"
    assert len(payload["exports"]) == 1
    export = payload["exports"][0]
    assert export["packet_id"] == "bedc-jepa-ledgered-world-state"
    assert export["claim_id"] == "bedc-jepa.ledgered-world-state-learning"
    assert export["claimed_layer"] == "world_model_readback"
    assert export["export_status"] in {"review_ready", "partial"}
    assert "boundary-gated latent recovery" in export["source_spec"]["can_test"]
    assert "official V-JEPA2-AC benchmark reproduction" in export["source_spec"]["cannot_test"]
    assert export["pattern_spec"]["systems"] == ["S0", "S1", "S2", "S3"]
    assert (
        export["pattern_spec"]["world_state_contract"]
        == "continuous latent state plus operational distinctions plus gap ledger"
    )
    assert export["classifier_spec"]["native_metric_contract_status"] == "contract_ready"
    assert export["classifier_spec"]["native_metric_template_status"] == "recorded"
    assert export["stability_spec"]["population_claim"] is False


def test_bedc_jepa_quality_lab_export_projects_metrics_and_boundaries():
    export = build_quality_lab_export()["exports"][0]
    metrics = export["metrics"]
    rows = {row["residue"]: row for row in export["ledger_rows"]}

    assert metrics["native_unlogged_error_reduction"] > 0.05
    assert metrics["native_planning_high_gap_reduction"] > 0.05
    assert metrics["vjepa2_ac_latent_prediction_score"] > 0.0
    assert metrics["full_retraining_loss_ablation_closed"] == 1.0
    assert metrics["public_baseline_native_metric_contract_recorded"] == 1.0
    assert metrics["public_baseline_native_metric_template_recorded"] == 1.0
    assert metrics["public_minigrid_calibration_row_count"] == 75.0
    assert metrics["public_minigrid_calibration_executed_row_count"] == 75.0
    assert metrics["public_minigrid_calibration_source_gap_row_count"] == 0.0
    assert metrics["public_minigrid_calibration_risk_reduction_mean"] > 0.0
    assert 0.0 <= metrics["public_minigrid_calibration_total_debt_direction_win_rate"] <= 1.0
    assert rows["public-baseline-native-metric-contract"]["status"] == "closed"
    assert rows["public-baseline-native-metric-contract"]["owner"] == OWNER
    assert rows["public-baseline-native-metric-template"]["status"] == "closed"
    assert rows["public-baseline-native-metric-template"]["owner"] == OWNER
    assert rows["official-vjepa2-ac-benchmark-reproduction"]["status"] == "open"
    assert rows["public-minigrid-total-debt-direction"]["status"] == "open"
    assert "public benchmark superiority" in export["not_claimed"]
    assert "official V-JEPA2-AC benchmark reproduction" in export["not_claimed"]


def test_bedc_jepa_quality_lab_export_records_artifact_fact_owner():
    export = build_quality_lab_export()["exports"][0]

    assert export["artifacts"]["paper"] == "papers/bedc_jepa/main.pdf"
    assert export["artifacts"]["native_metric_contract"] == (
        "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert export["artifacts"]["native_metric_template"] == (
        "reports/bedc_jepa_public_baseline_native_metric_template.json"
    )
    assert export["fact_owner"]["owner"] == OWNER
    assert "reports/bedc_jepa_review_bundle.json" in export["fact_owner"]["source_records"]
