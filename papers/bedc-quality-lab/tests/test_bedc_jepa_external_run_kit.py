from bedc_quality_lab.bedc_jepa_external_run_kit import build_external_run_kit


def test_external_run_kit_records_result_schemas_and_gate_conditions():
    kit = build_external_run_kit()

    assert kit["schema_id"] == "bedc-jepa-external-run-kit"
    assert kit["status"] == "contract_only"
    assert set(kit["required_external_results"]) == {
        "public_minigrid_execution",
        "public_jepa_baseline",
    }
    minigrid = kit["required_external_results"]["public_minigrid_execution"]
    baseline = kit["required_external_results"]["public_jepa_baseline"]

    assert minigrid["import_command"] == "python scripts/import_public_minigrid_benchmark_metrics.py <minigrid-result.json>"
    assert baseline["import_command"] == "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>"
    assert "gap_detection_auc" in minigrid["required_fields"]
    assert "latent_prediction_score" in baseline["required_fields"]
    assert minigrid["readiness_gate"] == "public_minigrid_execution"
    assert baseline["readiness_gate"] == "public_jepa_baseline"
    assert kit["readiness_command"] == "python scripts/build_bedc_jepa_readiness.py"
    assert (
        minigrid["export_command"]
        == "python scripts/export_public_minigrid_benchmark_result.py"
    )
    assert (
        baseline["export_command"]
        == "python scripts/export_public_jepa_baseline_result.py"
    )
