from bedc_quality_lab.public_benchmark_scope_contracts import (
    build_public_benchmark_scope_contracts,
)


def test_public_benchmark_scope_contracts_are_fail_closed():
    packet = build_public_benchmark_scope_contracts()

    assert packet["schema_id"] == "bedc-jepa-public-benchmark-scope-contracts"
    assert packet["status"] == "contract_ready"
    assert "public benchmark superiority" in packet["cannot_claim"]

    contracts = {row["contract_id"]: row for row in packet["contracts"]}
    assert set(contracts) == {
        "public_pixel_world_benchmark",
        "public_object_interaction_benchmark",
    }

    pixel = contracts["public_pixel_world_benchmark"]
    assert pixel["status"] == "contract_ready"
    assert pixel["current_result_status"] == "not_imported"
    assert pixel["source_gap_status"] == "source_gap_until_public_pixel_world_result_is_imported"
    assert "observation_preprocessing" in pixel["required_execution_fields"]
    assert "latent_or_rollout_metric" in pixel["required_execution_fields"]
    assert "unlogged_error" in pixel["required_bedc_metrics"]
    assert "public pixel-world benchmark superiority" in pixel["cannot_claim"]

    objects = contracts["public_object_interaction_benchmark"]
    assert objects["status"] == "contract_ready"
    assert objects["current_result_status"] == "not_imported"
    assert (
        objects["source_gap_status"]
        == "source_gap_until_public_object_interaction_result_is_imported"
    )
    assert "object_source_contract" in objects["required_execution_fields"]
    assert "distractor_or_clutter_contract" in objects["required_execution_fields"]
    assert "target_minus_distractor_masking_drop" in objects["required_bedc_metrics"]
    assert "public object-interaction benchmark superiority" in objects["cannot_claim"]

    assert "source gap" in pixel["claim_rule"]
    assert "source gap" in objects["claim_rule"]
