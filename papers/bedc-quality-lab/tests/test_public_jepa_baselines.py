from bedc_quality_lab.public_jepa_baselines import (
    build_public_jepa_cuda_adapter_comparison,
    build_public_jepa_adapter_comparison,
    build_public_jepa_baseline_external_result,
    build_public_jepa_baseline_probe,
    build_public_jepa_baseline_comparison,
    build_public_jepa_baseline_registry,
    run_public_jepa_ac_giant_adapter,
    run_public_jepa_structure_adapter,
    import_public_jepa_baseline_metrics,
)


def _native_metric_result():
    return {
        "candidate_id": "vjepa2-ac",
        "repository_commit": "abc123",
        "checkpoint_identity": "vjepa2_ac_test_checkpoint.pt",
        "dataset_identity": "MiniGrid-DoorKey-8x8-v0 stream",
        "environment_or_benchmark_name": "MiniGrid-DoorKey-8x8-v0",
        "execution_command": "python run_vjepa2_ac_baseline.py --env MiniGrid-DoorKey-8x8-v0",
        "observation_action_stream_contract": {
            "observation_preprocessing": "rgb frames",
            "action_encoding": "discrete actions",
            "split": "declared train/cal/test split",
        },
        "native_metric_contract": {
            "latent_prediction_score": "R2, higher is better",
            "rollout_or_planning_score": "success rate, higher is better",
        },
        "latent_prediction_score": 0.73,
        "rollout_or_planning_score": 0.61,
        "bedc_readback_metrics": {
            "distinction_accuracy": 0.8,
            "gap_detection_auc": 0.7,
            "unlogged_error": 0.1,
            "certified_coverage": 0.6,
            "debt": 0.2,
        },
        "lccp_certificate_metrics": {
            "alpha_grid": [0.2, 0.1, 0.05],
            "certified_claim_count": 1.0,
            "gap_claim_count": 2.0,
            "mean_certified_coverage": 0.7,
            "mean_unlogged_error": 0.03,
            "mean_conformal_miscoverage": 0.04,
        },
        "cannot_claim_boundary": [
            "public benchmark superiority unless comparative acceptance rule passes",
        ],
    }


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
    assert registry["execution_status"]["status"] in {
        "missing",
        "near_native_candidate_not_importable",
        "external_result_available",
    }
    if registry["execution_status"]["status"] == "near_native_candidate_not_importable":
        assert registry["execution_status"]["source_record"] == "reports/bedc_vjepa2_ac_native_reproduction.json"
        assert "native metric import contract" in registry["execution_status"]["reason"]
    if registry["execution_status"]["status"] == "external_result_available":
        assert registry["execution_status"]["source_record"] == "reports/bedc_vjepa2_ac_native_reproduction.json"
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
    assert comparison["native_metric_contract_source"] == (
        "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    )
    assert comparison["bedc_metrics_source"] == "reports/bedc_jepa_torch_objective.json"
    assert comparison["bedc_metrics_required"] == [
        "gap_auc_gain_mean",
        "unlogged_error_reduction_mean",
        "debt_reduction_mean",
        "latent_r2_delta_abs_max",
    ]
    assert "selected public baseline has not been executed" in comparison["remaining_requirement"]


def test_public_jepa_baseline_metrics_import_marks_comparison_executed():
    comparison = import_public_jepa_baseline_metrics(_native_metric_result())

    assert comparison["schema_id"] == "bedc-jepa-public-baseline-comparison"
    assert comparison["status"] == "executed"
    assert comparison["selected_candidate_id"] == "vjepa2-ac"
    assert comparison["execution_record"] == {
        "repository_commit": "abc123",
        "checkpoint_identity": "vjepa2_ac_test_checkpoint.pt",
        "dataset_identity": "MiniGrid-DoorKey-8x8-v0 stream",
        "environment_or_benchmark_name": "MiniGrid-DoorKey-8x8-v0",
        "execution_command": "python run_vjepa2_ac_baseline.py --env MiniGrid-DoorKey-8x8-v0",
        "observation_action_stream_contract": {
            "observation_preprocessing": "rgb frames",
            "action_encoding": "discrete actions",
            "split": "declared train/cal/test split",
        },
        "native_metric_contract": {
            "latent_prediction_score": "R2, higher is better",
            "rollout_or_planning_score": "success rate, higher is better",
        },
        "bedc_readback_metrics": {
            "distinction_accuracy": 0.8,
            "gap_detection_auc": 0.7,
            "unlogged_error": 0.1,
            "certified_coverage": 0.6,
            "debt": 0.2,
        },
        "lccp_certificate_metrics": {
            "alpha_grid": [0.2, 0.1, 0.05],
            "certified_claim_count": 1.0,
            "gap_claim_count": 2.0,
            "mean_certified_coverage": 0.7,
            "mean_unlogged_error": 0.03,
            "mean_conformal_miscoverage": 0.04,
        },
        "cannot_claim_boundary": [
            "public benchmark superiority unless comparative acceptance rule passes",
        ],
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
            "near_native_candidate_id",
            "repository_url",
            "repository_commit",
            "checkpoint_identity",
            "dataset_identity",
            "environment_or_benchmark_name",
            "execution_command",
            "observation_action_stream_contract",
            "native_metric_contract",
            "latent_prediction_score",
            "rollout_or_planning_score",
            "bedc_readback_metrics",
            "lccp_certificate_metrics",
            "cannot_claim_boundary",
            "cannot_export",
            "scope_boundary",
            "source_record",
        }
        assert result["near_native_candidate_id"] == "vjepa2-ac-vit-giant"
        assert result["repository_commit"] == "204698b45b3712590f06245fbfba32d3be539812"
        assert result["cannot_export"] == []
        assert "official V-JEPA2-AC benchmark protocol was not executed" in result["scope_boundary"]
        comparison = import_public_jepa_baseline_metrics(result)
        assert comparison["status"] == "executed"
    elif result["status"] == "near_native_candidate_not_importable":
        assert result["near_native_candidate_id"] == "vjepa2-ac-vit-giant"
        assert result["latent_prediction_score"] > 0.0
        assert result["rollout_or_planning_score"] > 0.0
        assert "repository commit is not recorded" in result["cannot_export"][0]
        assert "official V-JEPA2-AC benchmark protocol was not executed" in result["scope_boundary"]
        assert result["source_record"] == "reports/bedc_vjepa2_ac_native_reproduction.json"
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
    assert probe["status"] in {"structure_loaded", "metrics_import_ready", "unavailable"}
    assert "hub_cache_present" in probe
    assert "model_load_attempt" in probe

    if probe["status"] == "metrics_import_ready":
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
        assert probe["status"] in {"structure_loaded", "metrics_import_ready"}
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


def test_public_jepa_ac_giant_adapter_fails_closed_without_cuda(monkeypatch):
    monkeypatch.setattr(
        "bedc_quality_lab.public_jepa_baselines._cuda_environment_report",
        lambda: {"cuda_available": False, "torch_version": "test"},
    )

    result = run_public_jepa_ac_giant_adapter(train_count=2, test_count=2)

    assert result["schema_id"] == "bedc-jepa-public-ac-giant-adapter"
    assert result["status"] == "unavailable"
    assert result["candidate_id"] == "vjepa2-ac-vit-giant"
    assert "torch.cuda.is_available() is false" in result["remaining_requirement"]
    assert "V-JEPA2-AC action-conditioned checkpoint comparison" in result["cannot_claim"]


def test_public_jepa_cuda_comparison_records_ac_giant_deltas():
    comparison = build_public_jepa_cuda_adapter_comparison(
        bedc_objective={
            "distinction_accuracy": 0.98,
            "unlogged_error_rate": 0.0,
            "gap_detection_auc": 0.99,
            "certified_coverage": 0.91,
            "bedc_debt_score": 0.01,
        },
        ac_giant_adapter={
            "status": "available",
            "metrics": {
                "distinction_accuracy": 0.75,
                "unlogged_error_rate": 0.25,
                "gap_detection_auc": 0.40,
                "certified_coverage": 0.80,
                "bedc_debt_score": 0.20,
            },
        },
    )

    assert comparison["schema_id"] == "bedc-jepa-public-cuda-adapter-comparison"
    assert comparison["status"] == "executed"
    assert comparison["deltas"]["ac_giant_minus_bedc_distinction_accuracy"] == -0.22999999999999998
    assert comparison["deltas"]["ac_giant_minus_bedc_unlogged_error"] == 0.25
    assert comparison["deltas"]["ac_giant_minus_bedc_gap_auc"] == -0.59
    assert comparison["deltas"]["ac_giant_minus_bedc_debt"] == 0.19


def test_public_jepa_cuda_comparison_fails_closed_when_ac_missing():
    comparison = build_public_jepa_cuda_adapter_comparison(
        bedc_objective={
            "distinction_accuracy": 0.98,
            "unlogged_error_rate": 0.0,
            "gap_detection_auc": 0.99,
            "certified_coverage": 0.91,
            "bedc_debt_score": 0.01,
        },
        ac_giant_adapter={
            "status": "unavailable",
            "remaining_requirement": "checkpoint boundary missing",
        },
    )

    assert comparison["status"] == "missing_boundary"
    assert "V-JEPA2-AC action-conditioned checkpoint comparison" in comparison["cannot_claim"]
