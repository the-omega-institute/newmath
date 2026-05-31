from scripts.build_bedc_jepa_artifact_manifest import build_manifest
from scripts.run_bedc_jepa_experiment import run_experiment


def test_bedc_jepa_artifact_manifest_records_contact_ready_claims():
    manifest = build_manifest(run_experiment())

    assert manifest["schema_id"] == "bedc-jepa-artifact-manifest"
    assert manifest["artifact"] == "reports/bedc_jepa_four_system_experiment.json"
    assert manifest["commands"]["generate"] == "python scripts/run_bedc_jepa_experiment.py"
    assert manifest["commands"]["torch_objective"] == "python scripts/run_torch_bedc_jepa.py"
    assert manifest["commands"]["public_minigrid_probe"] == "python scripts/probe_public_minigrid.py"
    assert (
        manifest["commands"]["public_jepa_baseline_registry"]
        == "python scripts/build_public_jepa_baseline_registry.py"
    )
    assert manifest["commands"]["readiness"] == "python scripts/build_bedc_jepa_readiness.py"
    assert manifest["commands"]["test"] == "python -m pytest -q"
    assert manifest["objective_artifacts"]["torch"] == "reports/bedc_jepa_torch_objective.json"
    assert manifest["readiness"] == "reports/bedc_jepa_readiness.json"
    assert manifest["public_baselines"]["jepa_registry"] == "reports/bedc_jepa_public_baseline_registry.json"
    assert manifest["public_adapters"]["minigrid"] == "reports/bedc_jepa_public_minigrid_probe.json"
    assert (
        manifest["public_adapters"]["minigrid_benchmark_packet"]
        == "reports/bedc_jepa_public_minigrid_benchmark_packet.json"
    )
    assert (
        manifest["public_adapters"]["minigrid_transition_packet"]
        == "reports/bedc_jepa_public_minigrid_transition_packet.json"
    )

    claims = manifest["contact_ready_claims"]
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

    assert "public JEPA implementation comparison" in manifest["cannot_claim"]
    assert "general autonomous intelligence" in manifest["cannot_claim"]
