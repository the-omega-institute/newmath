from bedc_quality_lab.public_jepa_baselines import (
    build_public_jepa_adapter_comparison,
    build_public_jepa_baseline_external_result,
    build_public_jepa_baseline_probe,
    build_public_jepa_baseline_comparison,
    build_public_jepa_baseline_registry,
    run_public_jepa_structure_adapter,
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


def test_public_jepa_baseline_probe_records_dependency_and_repository_boundary():
    probe = build_public_jepa_baseline_probe()

    assert probe["schema_id"] == "bedc-jepa-public-baseline-probe"
    assert probe["candidate_id"] == "vjepa2-ac"
    assert probe["repository_url"] == "https://github.com/facebookresearch/vjepa2"
    assert "torch" in probe["dependency_status"]
    assert "timm" in probe["dependency_status"]
    assert probe["status"] in {"structure_loaded", "ready_to_import_metrics", "unavailable"}
    assert "hub_cache_present" in probe
    assert "model_load_attempt" in probe

    if probe["status"] == "ready_to_import_metrics":
        assert probe["cannot_execute"] == []
    else:
        assert probe["cannot_execute"]


def test_public_jepa_baseline_probe_model_load_attempt_is_fail_closed():
    probe = build_public_jepa_baseline_probe()
    attempt = probe["model_load_attempt"]

    assert attempt["status"] in {"not_attempted", "loaded", "failed"}
    assert "stage" in attempt
    if attempt["status"] == "not_attempted":
        assert attempt["stage"] == "dependency_check"
        assert "missing dependencies" in attempt["reason"]
    if attempt["status"] == "loaded":
        assert probe["status"] in {"structure_loaded", "ready_to_import_metrics"}
        assert "model_type" in attempt
    if attempt["status"] == "failed":
        assert probe["status"] == "unavailable"
        assert "exception_type" in attempt


def test_public_jepa_structure_adapter_runs_small_public_encoder_scope():
    result = run_public_jepa_structure_adapter(train_count=4, test_count=4, seed=77)

    assert result["schema_id"] == "bedc-jepa-public-structure-adapter"
    assert result["candidate_id"] == "vjepa2-1-vit-base-384-structure"
    assert result["status"] == "available"
    assert result["model"]["pretrained"] is False
    assert result["model"]["checkpoint_status"] == "not_loaded"
    assert result["sample_counts"] == {"train": 4.0, "test": 4.0}
    assert result["metrics"]["unlogged_error_rate"] >= 0.0
    assert result["metrics"]["gap_detection_auc"] >= 0.0
    assert "checkpoint weights were not loaded" in result["cannot_claim"]


def test_public_jepa_pretrained_adapter_records_checkpoint_scope():
    result = run_public_jepa_structure_adapter(train_count=4, test_count=4, seed=77, pretrained=True)

    assert result["schema_id"] == "bedc-jepa-public-structure-adapter"
    assert result["candidate_id"] == "vjepa2-1-vit-base-384-pretrained"
    assert result["status"] in {"available", "unavailable"}
    if result["status"] == "available":
        assert result["model"]["pretrained"] is True
        assert result["model"]["checkpoint_status"] == "loaded"
        assert result["metrics"]["unlogged_error_rate"] >= 0.0
        assert "V-JEPA2-AC action-conditioned checkpoint comparison" in result["cannot_claim"]


def test_public_jepa_adapter_comparison_records_bedc_advantage_and_ac_boundary():
    comparison = build_public_jepa_adapter_comparison(
        bedc_objective={
            "unlogged_error_rate": 0.0,
            "gap_detection_auc": 0.99,
            "bedc_debt_score": 0.01,
        },
        structure_adapter={
            "status": "available",
            "metrics": {
                "unlogged_error_rate": 0.31,
                "gap_detection_auc": 0.66,
                "bedc_debt_score": 0.50,
            },
        },
        pretrained_adapter={
            "status": "available",
            "metrics": {
                "unlogged_error_rate": 0.18,
                "gap_detection_auc": 0.46,
                "bedc_debt_score": 0.19,
            },
        },
    )

    assert comparison["schema_id"] == "bedc-jepa-public-adapter-comparison"
    assert comparison["status"] == "executed"
    assert comparison["deltas"]["pretrained_minus_bedc_unlogged_error"] == 0.18
    assert comparison["deltas"]["structure_minus_bedc_debt"] == 0.49
    assert comparison["ac_giant_gate"]["status"] == "needs_gpu"
