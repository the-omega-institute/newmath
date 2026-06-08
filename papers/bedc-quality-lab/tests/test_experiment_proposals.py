import json

import pytest

from bedc_quality_lab.discovery_compiler import experiment_proposals
from scripts import run_discovery_map as discovery_map


def _write_sources(root):
    (root / "reports" / "canonical").mkdir(parents=True, exist_ok=True)
    (root / "reports" / "canonical" / "discovery_map.json").write_text(
        json.dumps(
            {
                "schema_id": "bedc-quality-lab:canonical-discovery-map",
                "artifact_id": "bedc-quality-lab:discovery-map",
                "generated_at": "fixture-time",
                "json_artifact": "reports/canonical/discovery_map.json",
                "markdown_artifact": "reports/canonical/discovery_map.md",
                "row_count": 1,
                "level_counts": {},
                "rows": [
                    {
                        "report": "gap-head-attribution-capsule",
                        "json_artifact": "reports/canonical/gap_head_attribution_capsule.json",
                        "markdown_artifact": "reports/canonical/gap_head_attribution_capsule.md",
                        "discovery_level": "D5-M",
                        "projection_status": "projected",
                        "evidence_pointer": "$.mechanism_evidence",
                        "audit_status": "valid",
                        "audit_reason": "",
                        "mechanism_status": "blocked",
                        "mechanism_level": "blocked",
                        "mechanism_pointer": "$.mechanism_evidence",
                        "mechanism_failed_gate": "$.mechanism_evidence.failed_gate",
                    }
                ],
                "coverage_matrix": {
                    "status": "fail-closed",
                    "hardgates": {gate: {"status": "pass", "reason": "pass"} for gate in discovery_map.COVERAGE_HARDGATE_IDS},
                    "cells": [
                        {
                            "component_id": "fixture-gap",
                            "canonical_owner_pointer": "reports/canonical/source.json:$",
                            "discovery_level_pointer": "reports/canonical/source.json:$.level",
                            "claim_verdict_pointer": "reports/canonical/source.json:$.claim",
                            "mechanism_certificate_pointer": None,
                            "debt_pointer": None,
                            "negative_witness_pointer": None,
                            "hardgate_status": "fail",
                            "hardgate_reason": "fixture",
                        }
                    ],
                },
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (root / "reports" / "canonical" / "negative_discovery_reports.json").write_text(
        json.dumps(
            {
                "rows": [
                    {
                        "report_id": "fixture-negative",
                        "failed_gate": "$.failed",
                    }
                ]
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (root / "reports" / "canonical" / "gap_head_attribution_capsule.json").write_text(
        json.dumps({"mechanism_evidence": {"failed_gate": "$.mechanism_evidence.failed_gate"}}) + "\n",
        encoding="utf-8",
    )
    (root / "reports" / "canonical" / "source.json").write_text(
        json.dumps({"level": "D1", "claim": "blocked"}) + "\n",
        encoding="utf-8",
    )


def test_experiment_proposal_sidecar_builds_pointer_only_rows(tmp_path):
    _write_sources(tmp_path)

    payload = experiment_proposals.build_experiment_proposals(tmp_path, generated_at="fixture-time")
    by_type = {row["proposal_type"]: row for row in payload["rows"]}

    assert payload["schema_id"] == "bedc-quality-lab:experiment-proposals"
    assert payload["canonical_role"] == "pointer_sidecar_not_CANONICAL_REPORTS"
    assert set(by_type) == {"d5m_blocked_followup", "negative_discovery_followup", "coverage_gap"}
    assert payload["row_count"] == 3
    assert payload["audit"]["status"] == "pass"
    assert by_type["coverage_gap"]["coverage_cell_pointer"].startswith(
        "reports/canonical/discovery_map.json:$.coverage_matrix.cells["
    )
    assert by_type["negative_discovery_followup"]["negative_report_pointer"].startswith(
        "reports/canonical/negative_discovery_reports.json:$.rows["
    )
    assert by_type["d5m_blocked_followup"]["mechanism_evidence_pointer"] == (
        "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence"
    )
    for row in payload["rows"]:
        assert row["proposal_id"].startswith("prop:")
        assert isinstance(row["deterministic_toy_seed"], int)
        assert row["claim_capsule_draft"]["schema_id"] == "bedc.quality.claim_capsule.draft"
        assert "No production readiness claim is made." in row["not_claimed"]
        assert "No global superiority claim is made." in row["not_claimed"]


def test_experiment_proposal_validation_rejects_owner_fact_copies(tmp_path):
    _write_sources(tmp_path)
    payload = experiment_proposals.build_experiment_proposals(tmp_path, generated_at="fixture-time")

    forbidden = {
        "next_hypothesis": "fixture",
        "what_was_learned": "fixture",
        "terminal_verdict": "negative_discovery",
        "classifier_reasons": ["fixture"],
        "downgrade_reason": "fixture",
        "metrics": {"score": 1},
        "raw_metrics": [{"score": 1}],
    }
    for key, value in forbidden.items():
        mutated = {**payload, "rows": [{**payload["rows"][0], key: value}, *payload["rows"][1:]]}
        with pytest.raises(ValueError, match="copies source owner facts"):
            experiment_proposals.validate_experiment_proposal_payload(tmp_path, mutated)


def test_experiment_proposal_validation_rejects_claim_overreach(tmp_path):
    _write_sources(tmp_path)
    payload = experiment_proposals.build_experiment_proposals(tmp_path, generated_at="fixture-time")
    mutated = {
        **payload,
        "rows": [
            {
                **payload["rows"][0],
                "claim_capsule_draft": {
                    **payload["rows"][0]["claim_capsule_draft"],
                    "claim_intent": "production ready global superiority test",
                },
            },
            *payload["rows"][1:],
        ],
    }

    with pytest.raises(ValueError, match="copies source owner facts"):
        experiment_proposals.validate_experiment_proposal_payload(tmp_path, mutated)


def test_write_experiment_proposals_is_idempotent(tmp_path):
    _write_sources(tmp_path)

    first = experiment_proposals.write_experiment_proposals(tmp_path, generated_at="fixture-time")
    first_json = (tmp_path / experiment_proposals.JSON_ARTIFACT).read_text(encoding="utf-8")
    first_md = (tmp_path / experiment_proposals.MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    second = experiment_proposals.write_experiment_proposals(tmp_path, generated_at="fixture-time")

    assert first == second
    assert (tmp_path / experiment_proposals.JSON_ARTIFACT).read_text(encoding="utf-8") == first_json
    assert (tmp_path / experiment_proposals.MARKDOWN_ARTIFACT).read_text(encoding="utf-8") == first_md
