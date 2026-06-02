from bedc_quality_lab.bedc_jepa_external_run_kit import build_external_run_kit


def test_external_run_kit_records_result_schemas_and_gate_conditions():
    kit = build_external_run_kit()

    assert kit["schema_id"] == "bedc-jepa-external-run-kit"
    assert kit["status"] == "review_ready"
    assert set(kit["required_external_results"]) == {
        "public_jepa_checkpoint_contact",
        "public_minigrid_execution",
        "public_jepa_baseline",
    }
    checkpoint = kit["required_external_results"]["public_jepa_checkpoint_contact"]
    minigrid = kit["required_external_results"]["public_minigrid_execution"]
    baseline = kit["required_external_results"]["public_jepa_baseline"]

    assert checkpoint["readiness_gate"] == "public_jepa_checkpoint_contact"
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
    assert kit["readiness_command"] == "python scripts/build_bedc_jepa_readiness.py"
    assert kit["review_bundle_command"] == "python scripts/build_bedc_jepa_review_bundle.py"
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
