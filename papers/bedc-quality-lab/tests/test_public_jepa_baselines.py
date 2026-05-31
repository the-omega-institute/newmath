from bedc_quality_lab.public_jepa_baselines import (
    build_public_jepa_baseline_external_result,
    build_public_jepa_baseline_comparison,
    build_public_jepa_baseline_registry,
    import_public_jepa_baseline_metrics,
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


def test_public_jepa_baseline_metrics_import_marks_comparison_executed():
    comparison = import_public_jepa_baseline_metrics(
        {
            "candidate_id": "vjepa2-ac",
            "commit": "abc123",
            "checkpoint": "vjepa2_ac_test_checkpoint.pt",
            "reported_benchmark_name": "MiniGrid-DoorKey-8x8-v0",
            "latent_prediction_score": 0.73,
            "rollout_or_planning_score": 0.61,
        }
    )

    assert comparison["schema_id"] == "bedc-jepa-public-baseline-comparison"
    assert comparison["status"] == "executed"
    assert comparison["selected_candidate_id"] == "vjepa2-ac"
    assert comparison["execution_record"] == {
        "commit": "abc123",
        "checkpoint": "vjepa2_ac_test_checkpoint.pt",
    }
    assert comparison["baseline_metrics"] == {
        "latent_prediction_score": 0.73,
        "rollout_or_planning_score": 0.61,
        "reported_benchmark_name": "MiniGrid-DoorKey-8x8-v0",
    }
    assert comparison["cannot_claim"] == []


def test_public_jepa_baseline_external_result_records_execution_boundary():
    result = build_public_jepa_baseline_external_result()

    assert result["candidate_id"] == "vjepa2-ac"
    assert result["repository_url"] == "https://github.com/facebookresearch/vjepa2"

    if result["status"] == "available":
        assert set(result) == {
            "status",
            "candidate_id",
            "repository_url",
            "commit",
            "checkpoint",
            "reported_benchmark_name",
            "latent_prediction_score",
            "rollout_or_planning_score",
        }
        comparison = import_public_jepa_baseline_metrics(result)
        assert comparison["status"] == "executed"
    else:
        assert result["status"] == "unavailable"
        assert result["cannot_export"] == [
            "public JEPA-family baseline was not executed in this workspace"
        ]
