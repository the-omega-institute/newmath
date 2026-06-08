import json

import pytest

from bedc_quality_lab.backends import model_discovery


def test_dgt_refs_are_pointer_only():
    refs = model_discovery.discovery_gated_transformer_refs()

    assert refs["owner_pointer"] == "reports/canonical/discovery-gated-transformer.json:$"
    assert refs["new_model_hardgates_pointer"] == "reports/canonical/new_model_hardgates.json:$.gates"
    assert all(isinstance(value, str) and ":" in value for value in refs.values())
    model_discovery.assert_pointer_only(refs)


def test_dgt_projection_metadata_excludes_copied_measurements():
    metadata = model_discovery.DGT_PROJECTION_METADATA
    serialized = json.dumps(metadata, sort_keys=True).lower()

    assert metadata["surface"] == "pointer-only"
    for forbidden in (
        '"accuracy"',
        '"loss"',
        '"records"',
        '"raw_metrics"',
        "hardgate.gates",
        "raw positive claim",
        "terminal_verdict",
    ):
        assert forbidden not in serialized
    model_discovery.assert_pointer_only(metadata)


def test_dgt_refs_reject_copied_measurement_field():
    refs = model_discovery.discovery_gated_transformer_refs()
    refs["accuracy"] = "reports/canonical/discovery-gated-transformer.json:$.component_refs"

    with pytest.raises(ValueError, match="copied field"):
        model_discovery.assert_pointer_only(refs)


def test_dgt_refs_reject_raw_positive_claim_prose():
    refs = model_discovery.discovery_gated_transformer_refs()
    refs["claim_text_pointer"] = "raw positive claim prose copied into the backend refs"

    with pytest.raises(ValueError, match="raw positive claim prose"):
        model_discovery.assert_pointer_only(refs)
