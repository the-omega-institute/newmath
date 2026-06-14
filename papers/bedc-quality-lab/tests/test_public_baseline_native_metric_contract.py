import pytest

from bedc_quality_lab.public_baseline_native_metric_contract import (
    BEDC_READBACK_FIELDS,
    LCCP_FIELDS,
    REQUIRED_EXECUTION_FIELDS,
    build_public_baseline_native_metric_contract,
    build_public_baseline_native_metric_template,
    validate_public_baseline_native_metric_result,
)


def _valid_result():
    return {
        "candidate_id": "vjepa2-ac",
        "repository_commit": "abc123",
        "checkpoint_identity": "vjepa2-ac-vitg.pt",
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
        "bedc_readback_metrics": {field: 0.5 for field in BEDC_READBACK_FIELDS},
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


def test_public_baseline_native_metric_contract_records_required_fields():
    contract = build_public_baseline_native_metric_contract()

    assert contract["schema_id"] == "bedc-jepa-public-baseline-native-metric-contract"
    assert contract["status"] == "contract_ready"
    assert contract["selected_candidate_id"] == "vjepa2-ac"
    assert contract["repository_url"] == "https://github.com/facebookresearch/vjepa2"
    assert tuple(contract["required_execution_fields"]) == REQUIRED_EXECUTION_FIELDS
    assert tuple(contract["native_metric_contract"]["bedc_readback_fields"]) == BEDC_READBACK_FIELDS
    assert tuple(contract["native_metric_contract"]["lccp_certificate_fields"]) == LCCP_FIELDS
    assert "same public observation/action stream" in contract["native_metric_contract"]["same_protocol_requirements"]
    assert "repository commit is recorded" in contract["native_metric_contract"]["native_result_requirements"]
    assert contract["current_status"]["official_protocol_execution"] == "not_evaluated"
    assert contract["current_status"]["fixed_checkpoint_metric_import"] in {"not_evaluated", "executed"}
    assert contract["current_status"]["near_native_record"] == "reports/bedc_vjepa2_ac_native_reproduction.json"
    assert contract["current_status"]["near_native_metric_importable"] in {"yes", "no"}
    assert "official V-JEPA2-AC benchmark reproduction" in contract["cannot_claim"]
    assert "public benchmark superiority" in contract["cannot_claim"]


def test_public_baseline_native_metric_contract_validates_result_shape():
    validate_public_baseline_native_metric_result(_valid_result())


def test_public_baseline_native_metric_template_is_fillable_without_claiming_execution():
    template = build_public_baseline_native_metric_template()

    assert template["schema_id"] == "bedc-jepa-public-baseline-native-metric-template"
    assert template["template_for"] == "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    assert template["candidate_id"] == "vjepa2-ac"
    assert tuple(template["required_execution_fields"]) == REQUIRED_EXECUTION_FIELDS
    assert set(template["result"]) == set(REQUIRED_EXECUTION_FIELDS)
    assert template["result"]["candidate_id"] == "vjepa2-ac"
    assert set(template["result"]["bedc_readback_metrics"]) == set(BEDC_READBACK_FIELDS)
    assert set(template["result"]["lccp_certificate_metrics"]) == set(LCCP_FIELDS)
    assert "executed external baseline result" in template["cannot_claim"]
    assert "public benchmark superiority" in template["cannot_claim"]


def test_public_baseline_native_metric_contract_rejects_missing_native_fields():
    result = _valid_result()
    del result["execution_command"]

    with pytest.raises(ValueError, match="execution_command"):
        validate_public_baseline_native_metric_result(result)


def test_public_baseline_native_metric_contract_rejects_unrecorded_source_identity():
    result = _valid_result()
    result["repository_commit"] = "not recorded by the fixed-checkpoint MiniGrid reports"

    with pytest.raises(ValueError, match="repository_commit"):
        validate_public_baseline_native_metric_result(result)


def test_public_baseline_native_metric_contract_rejects_missing_readback_metrics():
    result = _valid_result()
    del result["bedc_readback_metrics"]["debt"]

    with pytest.raises(ValueError, match="debt"):
        validate_public_baseline_native_metric_result(result)
