from __future__ import annotations

import json
from pathlib import Path

import pytest

from bedc_quality_lab import reproduction_package as repro
ROOT = Path(__file__).resolve().parents[1]


def test_reproduction_package_schema_and_pointer_boundaries():
    payload = repro.build_package(ROOT, generated_at="fixture")

    assert payload["schema_id"] == "bedc-quality-lab:reproduction-package"
    assert payload["artifact_id"] == "bedc-quality-lab:reproduction-package"
    assert payload["producer"] == "scripts/run_reproduction_package.py"
    assert payload["claim_capsule_ref"]["owner_pointer"] == "reports/canonical/claim_capsule.json:$"
    assert "reproduction_targets" in payload
    assert "projection_regen_refs" in payload
    assert set(payload["hardgates"]) == {"REPRO-HG1", "REPRO-HG2", "REPRO-HG3", "REPRO-HG4", "REPRO-HG5"}

    serialized = json.dumps(payload, sort_keys=True)
    assert "accuracy_mean" not in serialized
    assert "fair_decision" not in serialized
    assert "ladder_state" not in serialized
    assert "tolerance_range" not in serialized


def test_reproduction_package_structural_profile_reports_upstream_gap_without_failure():
    package = repro.build_package(ROOT, generated_at="fixture")
    result = repro.verify_package(package, ROOT, "structural", generated_at="fixture")
    rows = {row["target_id"]: row for row in result["target_results"]}

    assert rows["dgt-l0-honest-rerun"]["status"] == "pass"
    assert rows["honest-ablation-null-training"]["status"] == "pass"
    assert rows["fair-l1-training"]["status"] == "blocked"
    assert rows["fair-l1-training"]["fingerprint_status"] == "pass"
    assert "fair-l1-training" in result["blocked_targets"]
    assert result["failed_targets"] == []


def test_reproduction_package_projection_profile_excludes_full_repro_rows():
    package = repro.build_package(ROOT, generated_at="fixture")
    result = repro.verify_package(package, ROOT, "projection", generated_at="fixture")

    assert result["profile"] == "projection"
    assert result["target_results"]
    assert {row["target_kind"] for row in result["target_results"]} == {"projection-only"}
    assert "fair-l1-training" not in {row["target_id"] for row in result["target_results"]}


def test_reproduction_package_full_profile_does_not_accept_projection_target():
    package = repro.build_package(ROOT, generated_at="fixture")
    result = repro.verify_package(
        package,
        ROOT,
        "full-repro-ci",
        target_ids=("canonical-index-view",),
        generated_at="fixture",
    )

    assert result["target_results"][0]["status"] == "blocked"
    assert "full-repro-ci profile cannot target projection-only rows" in result["target_results"][0]["failure_reasons"]


def test_reproduction_package_missing_seed_refs_fails_closed():
    package = repro.build_package(ROOT, generated_at="fixture")
    mutated = json.loads(json.dumps(package))
    target = next(row for row in mutated["reproduction_targets"] if row["target_id"] == "dgt-l0-honest-rerun")
    target["seed_refs"] = []

    with pytest.raises(ValueError, match="full reproduction refs incomplete"):
        repro.validate_package(mutated, ROOT)


def test_reproduction_package_projection_only_cannot_enter_full_repro_list():
    package = repro.build_package(ROOT, generated_at="fixture")
    mutated = json.loads(json.dumps(package))
    target = next(row for row in mutated["reproduction_targets"] if row["target_id"] == "canonical-index-view")
    target["target_kind"] = "full-repro-ci"

    with pytest.raises(ValueError, match="projection-only target listed as full reproduction"):
        repro.validate_package(mutated, ROOT)


def test_reproduction_package_missing_data_generator_ref_blocks_target():
    package = repro.build_package(ROOT, generated_at="fixture")
    mutated = json.loads(json.dumps(package))
    target = next(row for row in mutated["reproduction_targets"] if row["target_id"] == "dgt-l0-honest-rerun")
    target["data_generator_ref"] = "reports/canonical/missing-owner.json:$"

    result = repro.verify_package(mutated, ROOT, "structural", target_ids=("dgt-l0-honest-rerun",), generated_at="fixture")

    assert result["target_results"][0]["status"] == "blocked"
    assert any("pointer does not resolve" in reason for reason in result["target_results"][0]["failure_reasons"])


def test_reproduction_package_copied_owner_fact_is_rejected():
    package = repro.build_package(ROOT, generated_at="fixture")
    mutated = json.loads(json.dumps(package))
    mutated["reproduction_targets"][0]["accuracy_mean"] = 1.0

    with pytest.raises(ValueError, match="copied owner facts are forbidden"):
        repro.validate_package(mutated, ROOT)
