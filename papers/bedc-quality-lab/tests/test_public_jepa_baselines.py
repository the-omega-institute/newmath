from bedc_quality_lab.public_jepa_baselines import (
    build_public_jepa_baseline_comparison,
    build_public_jepa_baseline_registry,
)


def test_public_jepa_baseline_registry_records_action_conditioned_candidates():
    registry = build_public_jepa_baseline_registry()

    assert registry["schema_id"] == "bedc-jepa-public-baseline-registry"
    assert registry["status"] in {"contract_only", "executed"}
    assert registry["selected_candidate_id"] == "vjepa2-ac"
    assert {"vjepa2-ac", "leworldmodel-lejepa"} <= {
        candidate["candidate_id"] for candidate in registry["candidates"]
    }

    selected = next(
        candidate for candidate in registry["candidates"] if candidate["candidate_id"] == registry["selected_candidate_id"]
    )
    assert selected["baseline_role"] == "action-conditioned latent world-model baseline"
    assert selected["repository_url"] == "https://github.com/facebookresearch/vjepa2"
    assert "action-conditioned" in selected["why_relevant"]
    assert registry["execution_status"]["status"] == "missing"
    assert "clone or vendor the selected public baseline in an approved environment" in registry["next_actions"]


def test_public_jepa_baseline_comparison_records_missing_execution_contract():
    comparison = build_public_jepa_baseline_comparison()

    assert comparison["schema_id"] == "bedc-jepa-public-baseline-comparison"
    assert comparison["status"] == "missing"
    assert comparison["selected_candidate_id"] == "vjepa2-ac"
    assert comparison["baseline_metrics"] == {
        "latent_prediction_score": None,
        "rollout_or_planning_score": None,
        "reported_benchmark_name": None,
    }
    assert comparison["bedc_metrics_source"] == "reports/bedc_jepa_torch_objective.json"
    assert comparison["bedc_metrics_required"] == [
        "gap_auc_gain_mean",
        "unlogged_error_reduction_mean",
        "debt_reduction_mean",
        "latent_r2_delta_abs_max",
    ]
    assert "selected public baseline has not been executed" in comparison["blocking_reason"]
