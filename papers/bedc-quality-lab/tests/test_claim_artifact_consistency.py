import json
from pathlib import Path

import pytest

from bedc_quality_lab.artifact_freshness import canonical_artifact_hash
from bedc_quality_lab.claim_artifact_consistency import (
    CLAIM_GRAPH_ARTIFACT,
    CLAIM_VERDICTS_ARTIFACT,
    DGT_ARTIFACT,
    DGT_CLAIM_ID,
    DISCOVERY_MAP_ARTIFACT,
    HIGH_IMPACT_REVIEW_FINGERPRINT_ARTIFACT,
    HIGH_IMPACT_REVIEW_ARTIFACT,
    QUALITY_SCORECARD_ARTIFACT,
    audit_claim_artifact_consistency,
)
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.evidence_provenance import evidence_provenance_pointer_for_report
from scripts import run_discovery_map as discovery_map
from bedc_quality_lab.verdict import QUALITY_SCORECARD_METRICS
from scripts.run_claim_artifact_consistency import write_claim_artifact_consistency


def _write_json(root: Path, artifact: str, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_jsonl(root: Path, artifact: str, rows):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def _scorecard():
    return {
        "artifact_id": "bedc-quality-lab:quality-scorecard",
        "rows": [
            {"metric": metric, "status": "ready", "value": index}
            for index, metric in enumerate(QUALITY_SCORECARD_METRICS)
        ],
    }


def _anti_triviality_contract():
    return {
        "anti_triviality_status": "pass",
        "owner_contract": {
            "scale_only": {"status": "present"},
            "metadata_only": {"status": "present"},
            "matched_random": {"status": "present"},
            "forbidden_column": {"status": "present"},
        },
    } | owner_local_anti_triviality_contract(
        recommended_level="D4",
        scale_only_pointer="$.d4_projection.owner_contract.scale_only",
        metadata_only_pointer="$.d4_projection.owner_contract.metadata_only",
        matched_random_pointer="$.d4_projection.owner_contract.matched_random",
        forbidden_column_pointer="$.d4_projection.owner_contract.forbidden_column",
    )


def _fixture_root(tmp_path: Path) -> Path:
    root = tmp_path
    _write_json(root, QUALITY_SCORECARD_ARTIFACT, _scorecard())
    _write_json(root, "reports/canonical/formal_hardening.json", {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
    _write_json(
        root,
        DGT_ARTIFACT,
        {
            "artifact_id": "bedc-quality-lab:discovery-gated-transformer",
            "d4_projection_ref": {"artifact": DGT_ARTIFACT, "pointer": "$.d4_projection"},
            "d4_projection": {
                "discovery_level": "D4",
                "core_contracts": {
                    "claim_graph_owner": "Core",
                    "claim_verdict_owner": "Core",
                    "discovery_map_level_pointer": f"{DGT_ARTIFACT}:$.d4_projection.discovery_level",
                },
                "not_claimed": ["bounded toy projection only"],
                **_anti_triviality_contract(),
            },
            "hardgate": {"status": "pass"},
            "not_claimed": ["bounded deterministic toy evidence only"],
        },
    )
    scorecard_hash = canonical_artifact_hash(root / QUALITY_SCORECARD_ARTIFACT)
    _write_jsonl(
        root,
        CLAIM_VERDICTS_ARTIFACT,
        [
            {
                "claim_graph_node_id": "terminal:discovery-gated-transformer",
                "claim_id": DGT_CLAIM_ID,
                "claim_verdict": "accepted_positive_discovery",
                "formal_hardening_ready": True,
                "ledger_pointer": f"{HIGH_IMPACT_REVIEW_ARTIFACT}:$.review_rows[0]",
                "reason": "positive-discovery-gates-pass",
                "scorecard_hash": scorecard_hash,
                "scorecard_pointer": f"{QUALITY_SCORECARD_ARTIFACT}:$.rows",
                "scorecard_ready": True,
                "source": f"{DGT_ARTIFACT}:$.d4_projection",
            }
        ],
    )
    _write_json(
        root,
        DISCOVERY_MAP_ARTIFACT,
        {
            "rows": [
                {
                    "report": "discovery-gated-transformer",
                    "json_artifact": DGT_ARTIFACT,
                    "markdown_artifact": "reports/canonical/discovery-gated-transformer.md",
                    "discovery_level": "D4",
                    "evidence_pointer": "$.d4_projection",
                    "evidence_type": "deterministic_projection",
                    "evidence_provenance_pointer": evidence_provenance_pointer_for_report("discovery-gated-transformer"),
                    "scorecard_pointer": f"{QUALITY_SCORECARD_ARTIFACT}:$.rows",
                    "projection_status": "projected",
                    "audit_status": "valid",
                    "audit_reason": "",
                }
            ],
            "coverage_matrix": {
                "status": "pointer-only",
                "hardgates": {gate: {"status": "pass", "reason": "pass"} for gate in discovery_map.COVERAGE_HARDGATE_IDS},
                "cells": [
                    {
                        "component_id": "DGT",
                        "canonical_owner_pointer": f"{DGT_ARTIFACT}:$",
                        "discovery_level_pointer": f"{DGT_ARTIFACT}:$.d4_projection.discovery_level",
                        "claim_verdict_pointer": f"{DGT_ARTIFACT}:$.hardgate.status",
                        "mechanism_certificate_pointer": f"{DGT_ARTIFACT}:$.d4_projection",
                        "debt_pointer": f"{DGT_ARTIFACT}:$.d4_projection",
                        "negative_witness_pointer": None,
                        "hardgate_status": "pass",
                        "hardgate_reason": "pass",
                    }
                ],
            },
        },
    )
    _write_json(
        root,
        CLAIM_GRAPH_ARTIFACT,
        {
            "nodes": [
                {
                    "node_id": "raw:discovery-gated-transformer",
                    "node_type": "raw_evidence",
                    "source_pointer": f"{DGT_ARTIFACT}:$.d4_projection",
                    "depends_on": [],
                    "discovery_level": None,
                    "terminal_verdict": None,
                    "not_claimed": [],
                },
                {
                    "node_id": "projected:discovery-gated-transformer",
                    "node_type": "projected_discovery",
                    "source_pointer": f"{DISCOVERY_MAP_ARTIFACT}:$.rows[0]",
                    "depends_on": ["raw:discovery-gated-transformer"],
                    "discovery_level": "D4",
                    "terminal_verdict": None,
                    "not_claimed": [],
                },
                {
                    "node_id": "terminal:discovery-gated-transformer",
                    "node_type": "terminal_claim",
                    "source_pointer": f"{CLAIM_VERDICTS_ARTIFACT}:$.lines[0]",
                    "depends_on": ["projected:discovery-gated-transformer"],
                    "discovery_level": None,
                    "terminal_verdict": "accepted_positive_discovery",
                    "not_claimed": [],
                },
            ]
        },
    )
    _write_json(root, HIGH_IMPACT_REVIEW_ARTIFACT, {"review_rows": [{"claim_id": DGT_CLAIM_ID}], "not_claimed": ["bounded"]})
    _write_json(
        root,
        HIGH_IMPACT_REVIEW_FINGERPRINT_ARTIFACT,
        {
            "inputs": {
                "source_artifacts": [
                    {"path": DGT_ARTIFACT, "sha256": canonical_artifact_hash(root / DGT_ARTIFACT)},
                    {"path": CLAIM_GRAPH_ARTIFACT, "sha256": canonical_artifact_hash(root / CLAIM_GRAPH_ARTIFACT)},
                ]
            }
        },
    )
    return root


def _gate(report, gate_id):
    return next(gate for gate in report.gates if gate.gate_id == gate_id)


def test_cons_hg1_dgt_level_and_verdict_are_coherent(tmp_path):
    root = _fixture_root(tmp_path)

    report = audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")

    assert report.status == "pass"
    assert _gate(report, "CONS-HG1").status == "pass"

    payload = json.loads((root / DISCOVERY_MAP_ARTIFACT).read_text(encoding="utf-8"))
    payload["rows"][0]["discovery_level"] = "D3"
    _write_json(root, DISCOVERY_MAP_ARTIFACT, payload)

    report = audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")

    assert report.status == "fail"
    assert _gate(report, "CONS-HG1").status == "fail"


def test_default_api_audits_dgt_claim(tmp_path):
    root = _fixture_root(tmp_path)

    report = audit_claim_artifact_consistency(root, generated_at="fixture-time")

    assert report.claim_id == DGT_CLAIM_ID
    assert report.status == "pass"


def test_cons_hg2_positive_verdict_requires_current_scorecard_hash(tmp_path):
    root = _fixture_root(tmp_path)
    rows = [json.loads(line) for line in (root / CLAIM_VERDICTS_ARTIFACT).read_text(encoding="utf-8").splitlines()]
    rows[0]["scorecard_hash"] = "stale"
    _write_jsonl(root, CLAIM_VERDICTS_ARTIFACT, rows)

    report = audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")

    assert _gate(report, "CONS-HG2").status == "fail"


def test_cons_hg3_reason_scorecard_ready_taxonomy_is_consistent(tmp_path):
    root = _fixture_root(tmp_path)
    rows = [json.loads(line) for line in (root / CLAIM_VERDICTS_ARTIFACT).read_text(encoding="utf-8").splitlines()]
    rows[0]["scorecard_ready"] = False
    _write_jsonl(root, CLAIM_VERDICTS_ARTIFACT, rows)

    report = audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")

    assert _gate(report, "CONS-HG3").status == "fail"

    rows[0]["reason"] = "scorecard-not-ready"
    rows[0]["scorecard_ready"] = True
    _write_jsonl(root, CLAIM_VERDICTS_ARTIFACT, rows)
    report = audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")

    assert _gate(report, "CONS-HG3").status == "fail"


def test_cons_hg4_terminal_node_points_to_dgt_d4_projection(tmp_path):
    root = _fixture_root(tmp_path)
    graph = json.loads((root / CLAIM_GRAPH_ARTIFACT).read_text(encoding="utf-8"))
    graph["nodes"][2]["depends_on"] = []
    _write_json(root, CLAIM_GRAPH_ARTIFACT, graph)
    _write_json(
        root,
        HIGH_IMPACT_REVIEW_FINGERPRINT_ARTIFACT,
        {
            "inputs": {
                "source_artifacts": [
                    {"path": DGT_ARTIFACT, "sha256": canonical_artifact_hash(root / DGT_ARTIFACT)},
                    {"path": CLAIM_GRAPH_ARTIFACT, "sha256": canonical_artifact_hash(root / CLAIM_GRAPH_ARTIFACT)},
                ]
            }
        },
    )

    report = audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")

    assert _gate(report, "CONS-HG4").status == "fail"


def test_cons_hg5_coverage_matrix_dgt_cell_points_to_owner(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / DISCOVERY_MAP_ARTIFACT).read_text(encoding="utf-8"))
    payload["coverage_matrix"]["cells"][0]["canonical_owner_pointer"] = "reports/canonical/missing.json:$"
    _write_json(root, DISCOVERY_MAP_ARTIFACT, payload)

    with pytest.raises(ValueError, match="coverage_matrix COV-HG1-owner status mismatch"):
        audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (lambda row: row.pop("evidence_type"), "requires owner evidence_type"),
        (lambda row: row.update({"evidence_type": None}), "requires owner evidence_type"),
        (
            lambda row: row.update(
                {
                    "evidence_provenance_pointer": (
                        "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.missing"
                    )
                }
            ),
            "requires owner evidence provenance pointer",
        ),
    ],
)
def test_claim_artifact_consistency_validates_committed_discovery_map_before_audit(tmp_path, mutate, message):
    root = _fixture_root(tmp_path)
    path = root / DISCOVERY_MAP_ARTIFACT
    payload = json.loads(path.read_text(encoding="utf-8"))
    mutate(payload["rows"][0])
    _write_json(root, DISCOVERY_MAP_ARTIFACT, payload)

    with pytest.raises(ValueError, match=message):
        audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")


def test_cons_hg6_stale_artifact_hash_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    graph = json.loads((root / CLAIM_GRAPH_ARTIFACT).read_text(encoding="utf-8"))
    graph["nodes"][0]["not_claimed"] = ["mutated"]
    _write_json(root, CLAIM_GRAPH_ARTIFACT, graph)

    report = audit_claim_artifact_consistency(root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")

    assert _gate(report, "CONS-HG6").status == "fail"


def test_runner_is_idempotent(tmp_path):
    root = _fixture_root(tmp_path)

    first = write_claim_artifact_consistency(root=root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")
    first_bytes = (root / "reports/canonical/claim-artifact-consistency.json").read_bytes()
    second = write_claim_artifact_consistency(root=root, claim_id=DGT_CLAIM_ID, generated_at="fixture-time")
    second_bytes = (root / "reports/canonical/claim-artifact-consistency.json").read_bytes()

    assert first == second
    assert first_bytes == second_bytes
