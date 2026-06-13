import json

import pytest

from bedc_quality_lab import dgt_l1_boundary_report as boundary
from bedc_quality_lab import dgt_l1_controls


def _write_l1_controls(root):
    payload = dgt_l1_controls.build_payload(generated_at="fixture-time", requested_device="cpu")
    dgt_l1_controls.write_artifacts(payload, root=root, generated_at="fixture-time")
    return payload


def test_boundary_payload_promotion_exclusion_is_exact(tmp_path):
    _write_l1_controls(tmp_path)

    payload = boundary.build_l1_boundary_report(root=tmp_path, generated_at="fixture-time")

    assert payload["artifact_role"] == "boundary_block"
    assert payload["claim_promotion_eligible"] is False
    assert payload["claim_promotion_exclusion"] == {
        "status": "not-eligible",
        "reason": "information-access-boundary",
        "excluded_surfaces": ["positive_claim_cells", "discovery_promotion", "l1-scaling"],
        "blocking_pointer": "$.scaling_claim_block",
        "fair_rebuild_required": True,
    }
    assert payload["scaling_claim_block"]["status"] == "blocked"
    assert payload["scaling_claim_block"]["runtime_pointer"] == "$.scaling_claim_block"
    boundary.validate_l1_boundary_report(payload)


def test_boundary_report_forbids_block_aliases(tmp_path):
    _write_l1_controls(tmp_path)
    payload = boundary.build_l1_boundary_report(root=tmp_path, generated_at="fixture-time")

    for alias in ("ladder_block", "claim_block"):
        mutated = json.loads(json.dumps(payload))
        mutated[alias] = {"status": "unblocked"}
        with pytest.raises(ValueError, match="forbidden aliases"):
            boundary.validate_l1_boundary_report(mutated)


def test_boundary_formula_cells_match_expected_l1_limits(tmp_path):
    _write_l1_controls(tmp_path)
    payload = boundary.build_l1_boundary_report(root=tmp_path, generated_at="fixture-time")

    assert boundary.base_bayes_ceiling() == 0.0625
    assert payload["base_bayes_ceiling"]["computed_value"] == 0.0625
    assert payload["table_coverage_ceiling"]["computed_value"] == pytest.approx(1 - ((255 / 256) ** 1024))
    assert payload["ood_solvability"]["status"] == "not-winnable-from-recorded-features"


def test_negative_witness_refs_are_pointer_only(tmp_path):
    _write_l1_controls(tmp_path)
    payload = boundary.build_l1_boundary_report(root=tmp_path, generated_at="fixture-time")

    assert {row["kind"] for row in payload["negative_witness_refs"]} == set(boundary.REQUIRED_WITNESSES)
    for row in payload["negative_witness_refs"]:
        assert set(row) == {"kind", "owner_artifact", "pointer", "owner_issue", "resolution_status"}
        assert row["owner_artifact"] == boundary.DGT_L1_CONTROLS_ARTIFACT
        assert row["owner_issue"] == 1207
        assert row["pointer"].startswith("reports/canonical/dgt-l1-controls.json:$.negative_witness_sweep.rows")


def test_scaling_claim_block_is_only_runtime_key(tmp_path):
    _write_l1_controls(tmp_path)
    payload = boundary.build_l1_boundary_report(root=tmp_path, generated_at="fixture-time")

    mutated = json.loads(json.dumps(payload))
    mutated["claim_promotion_exclusion"]["status"] = "eligible"
    mutated["not_claimed"] = []
    assert boundary.scaling_claim_block_allows_l1_scaling(mutated) is False

    mutated = json.loads(json.dumps(payload))
    mutated.pop("scaling_claim_block")
    assert boundary.scaling_claim_block_allows_l1_scaling(mutated) is False

    mutated = json.loads(json.dumps(payload))
    mutated["scaling_claim_block"]["status"] = "unblocked"
    mutated["scaling_claim_block"]["fair_rebuild_status"] = "unresolved"
    assert boundary.scaling_claim_block_allows_l1_scaling(mutated) is False

