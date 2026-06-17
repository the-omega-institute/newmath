from bedc_quality_lab.bedc_jepa_paper_writeback_packet import (
    OWNER,
    SCHEMA_ID,
    build_paper_writeback_packet,
)


def test_paper_writeback_packet_records_paper_ready_claim_boundary():
    packet = build_paper_writeback_packet()

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["status"] in {"paper_ready", "partial"}
    assert packet["source_records"]["quality_lab_export"] == "reports/bedc_jepa_quality_lab_exports.json"
    assert packet["metrics"]["readiness_decision"] == "external_bundle_ready"
    assert packet["metrics"]["native_unlogged_error_reduction"] > 0.05
    assert packet["metrics"]["vjepa2_ac_latent_prediction_score"] > 0.0
    assert packet["metrics"]["native_metric_contract_field_count"] >= 10.0
    assert packet["metrics"]["native_metric_template_result_field_count"] >= 10.0
    assert packet["metrics"]["public_minigrid_calibration_row_count"] == 75.0
    assert packet["metrics"]["public_minigrid_calibration_executed_row_count"] == 75.0
    assert packet["metrics"]["public_minigrid_calibration_source_gap_row_count"] == 0.0
    assert packet["metrics"]["public_minigrid_calibration_risk_reduction_mean"] > 0.0
    assert 0.0 <= packet["metrics"]["public_minigrid_calibration_total_debt_direction_win_rate"] <= 1.0
    assert packet["record"]["admitted_operational_name"] == "door_key_context_visible"
    assert "has_key" in packet["record"]["source_gap_predicates"]
    assert "public benchmark superiority" in packet["record"]["cannot_upgrade_to"]
    assert "official V-JEPA2-AC benchmark reproduction" in packet["not_claimed"]


def test_paper_writeback_packet_projects_rollup_sections():
    packet = build_paper_writeback_packet()

    assert "can_test" in packet["source_spec"]
    assert packet["pattern_spec"]["systems"] == ["S0", "S1", "S2", "S3"]
    assert packet["classifier_spec"]["native_metric_contract_status"] == "contract_ready"
    assert packet["stability_spec"]["population_claim"] is False
    rows = {row["residue"]: row for row in packet["ledger_rows"]}
    assert rows["public-baseline-native-metric-contract"]["status"] == "closed"
    assert rows["official-vjepa2-ac-benchmark-reproduction"]["status"] == "open"


def test_paper_writeback_packet_records_artifacts_and_fact_owner():
    packet = build_paper_writeback_packet()

    assert packet["artifacts"]["paper_source"] == "papers/bedc_jepa/main.tex"
    assert packet["artifacts"]["quality_lab_export"] == "reports/bedc_jepa_quality_lab_exports.json"
    assert packet["artifacts"]["native_metric_contract"] == (
        "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert packet["artifacts"]["native_metric_template"] == (
        "reports/bedc_jepa_public_baseline_native_metric_template.json"
    )
    assert packet["artifacts"]["public_minigrid_calibration_extension"] == (
        "reports/bedc_jepa_public_minigrid_calibration_extension.json"
    )
    assert packet["fact_owner"]["owner"] == OWNER
    assert packet["fact_owner"]["review_bundle_status"] == "review_ready"
