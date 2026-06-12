import json
from copy import deepcopy
from pathlib import Path

import pytest

from bedc_quality_lab import claim_graph
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.evidence_provenance import OWNER as EVIDENCE_PROVENANCE_OWNER
from bedc_quality_lab.evidence_provenance import SCHEMA_ID as EVIDENCE_PROVENANCE_SCHEMA_ID
from bedc_quality_lab.evidence_provenance import evidence_provenance_pointer_for_report
from bedc_quality_lab import high_impact_review
from scripts import run_canonical_reports as canonical
from scripts import run_claim_verdict_demo as claim_verdict_demo


def _write_json(root: Path, artifact: str, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _write_jsonl(root: Path, artifact: str, rows):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def _write_evidence_provenance_index(root: Path, rows, *, empirical_reports=("gap-head-discovery",)):
    producer_rows = []
    metric_rows = []
    discovery_rows = []
    for index, row in enumerate(rows):
        report = str(row["report"])
        is_empirical = report in set(empirical_reports)
        source_type = "measured_training" if is_empirical else "deterministic_projection"
        evidence_type = "empirical_training_clean" if is_empirical else "deterministic_projection"
        if row.get("discovery_level") == "DN":
            evidence_type = "boundary_negative"
            source_type = "deterministic_projection"
        row["evidence_type"] = evidence_type
        row["evidence_provenance_pointer"] = evidence_provenance_pointer_for_report(report)
        producer_rows.append(
            {
                "report": report,
                "producer_command": ["python3", "scripts/run_fixture.py"],
                "producer_source_pointer": "scripts/run_fixture.py",
                "backward_pointers": ["scripts/run_fixture.py:L2"] if is_empirical else [],
                "optimizer_step_pointers": ["scripts/run_fixture.py:L3"] if is_empirical else [],
                "parameter_update_pointers": [],
                "training_evidence_status": "empirical_training_clean" if is_empirical else "training_evidence_absent",
                "not_claimed": [] if is_empirical else ["fixture projection evidence"],
            }
        )
        metric_rows.append(
            {
                "report": report,
                "metric_name": "headline",
                "source_type": source_type,
                "source_code_pointer": "scripts/run_fixture.py",
                "source_artifact_pointer": f"{row['json_artifact']}:{row.get('evidence_pointer') or '$'}",
                "producer_training_audit_pointer": f"reports/canonical/index.json:$.evidence_provenance.producer_audits[{index}]",
                "allowed_for_empirical_claim": is_empirical,
                "value": True,
                "not_claimed": [] if is_empirical else ["fixture projection evidence"],
                "not_measurable_reason": None,
            }
        )
        discovery_rows.append(
            {
                "report": report,
                "evidence_type": evidence_type,
                "discovery_map_pointer": f"reports/canonical/discovery_map.json:$.rows[{index}]",
                "metric_provenance_pointers": [f"reports/canonical/index.json:$.evidence_provenance.metric_rows[{index}]"],
                "producer_training_audit_pointer": f"reports/canonical/index.json:$.evidence_provenance.producer_audits[{index}]",
                "allowed_claim_kinds": ["empirical_superiority"] if is_empirical else ["projection_only"],
                "not_claimed": [] if is_empirical else ["fixture projection evidence"],
            }
        )
    _write_json(
        root,
        "reports/canonical/index.json",
        {
            "schema_id": "bedc-quality-lab:canonical-report-index",
            "generated_at": "fixture",
            "evidence_provenance": {
                "schema_id": EVIDENCE_PROVENANCE_SCHEMA_ID,
                "owner": EVIDENCE_PROVENANCE_OWNER,
                "generated_at": "fixture",
                "producer_audits": producer_rows,
                "metric_rows": metric_rows,
                "discovery_rows": discovery_rows,
                "discovery_rows_by_report": {str(row["report"]): row for row in discovery_rows},
                "hardgate_status": {},
                "artifact_pointers": {"owner_pointer": "reports/canonical/index.json:$.evidence_provenance"},
            },
        },
    )


def _positive_owner_contract(level: str) -> dict[str, object]:
    return {
        "anti_triviality_status": "pass",
        "positive_discovery": True,
        "not_claimed": ["fixture"],
        "control": {"status": "present"},
        "scope": {"status": "present"},
        "owner_contract": {
            "scale_only": {"status": "present"},
            "metadata_only": ["fixture"],
            "matched_random": {"status": "present"},
            "forbidden_column": {"status": "present"},
        },
    } | owner_local_anti_triviality_contract(
        recommended_level=level,
        scale_only_pointer="$.owner_contract.scale_only",
        metadata_only_pointer="$.owner_contract.metadata_only",
        matched_random_pointer="$.owner_contract.matched_random",
        forbidden_column_pointer="$.owner_contract.forbidden_column",
    )


def _write_dgt_high_impact_review_pass(root: Path) -> None:
    hardgates = {
        gate_id: {
            "status": "pass",
            "reason": "fixture",
            "evidence_pointer": f"{high_impact_review.JSON_ARTIFACT}:$.not_claimed",
        }
        for gate_id in high_impact_review.HIR_GATE_IDS
    }
    hardgates["HIR-HG1"]["evidence_pointer"] = f"{high_impact_review.DGT_ARTIFACT}:$.d4_projection"
    hardgates["HIR-HG6"]["evidence_pointer"] = f"{high_impact_review.MODEL_COMPARISON_ARTIFACT}:$.hardgates"
    hardgates["HIR-HG7"]["evidence_pointer"] = f"{high_impact_review.MODEL_COMPARISON_ARTIFACT}:$.hardgates.MC-HG7"
    hardgates["HIR-HG8"]["evidence_pointer"] = f"{high_impact_review.MODEL_COMPARISON_ARTIFACT}:$.hardgates.MC-HG8"
    hardgates["HIR-HG9"]["evidence_pointer"] = f"{high_impact_review.MODEL_COMPARISON_ARTIFACT}:$.hardgates.MC-HG9"
    hardgates["HIR-HG10"]["evidence_pointer"] = f"{high_impact_review.CLAIM_GRAPH_ARTIFACT}:$.nodes"
    _write_json(
        root,
        high_impact_review.JSON_ARTIFACT,
        {
            "schema_id": high_impact_review.SCHEMA_ID,
            "artifact_id": high_impact_review.ARTIFACT_ID,
            "generated_at": "2030-01-01T00:00:00+00:00",
            "seed": 1131,
            "source_artifacts": {
                "dgt": high_impact_review.DGT_ARTIFACT,
                "model_comparison": high_impact_review.MODEL_COMPARISON_ARTIFACT,
                "claim_graph": high_impact_review.CLAIM_GRAPH_ARTIFACT,
            },
            "review_rows": [
                {
                    "claim_id": high_impact_review.DGT_CLAIM_ID,
                    "status": "pass",
                    "review_level": "bounded-D4-terminal-gate",
                    "review_scope": "DGT bounded deterministic toy D4 positive-discovery terminal promotion only",
                    "ledger_pointer": high_impact_review.DGT_REVIEW_ROW_POINTER,
                    "claim_pointer": f"{high_impact_review.DGT_ARTIFACT}:$.d4_projection",
                    "hardgate_pointer": f"{high_impact_review.JSON_ARTIFACT}:$.hardgates",
                    "not_claimed_pointer": f"{high_impact_review.JSON_ARTIFACT}:$.not_claimed",
                    "reason": "positive-discovery-gates-pass",
                }
            ],
            "hardgates": hardgates,
            "not_claimed": list(high_impact_review.NOT_CLAIMED),
        },
    )


def _write_dgt_owner_ref_fixtures(root: Path) -> None:
    _write_json(
        root,
        "reports/canonical/dgt-l0-controls.json",
        {
            "construct_suspension": {"status": "pass"},
            "honest_metric_review": {"status": "pass"},
            "negative_witness_sweep": {"status": "pass"},
            "compute_param_ledger": {"status": "pass"},
            "l0_toy_projection": {
                "status": "pass",
                "review_status": "pass",
                "hardgate_statuses": {"pass": {"status": "pass"}},
                "not_claimed": ["bounded L0 fixture"],
            },
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-l1-controls.json",
        {
            "negative_witness_sweep": {"status": "pass"},
            "l1_tiny_sequence_projection": {
                "review_status": "pass",
                "promotion_readiness": "ready-pass",
                "not_claimed": ["bounded L1 fixture"],
            },
            "l1_ood_mechanism": {
                "verdict": "fixture",
                "l2_implication": "not-claimed",
            },
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-neural-ablation.json",
        {
            "nabl_hardgates": {
                "status": "pass",
                "failed_gate": None,
            },
            "component_causal_claims": [],
        },
    )


def _row(claim_id, verdict):
    return {
        "claim_id": claim_id,
        "claim_graph_node_id": claim_graph.terminal_node_id_for_claim_id(claim_id),
        "claim_verdict": verdict,
        "reason": "fixture",
        "source": "reports/canonical/gap-head-discovery.json:$.positive_discovery",
        "ledger_pointer": "reports/canonical/discovery_map.json:$.rows[0].discovery_level",
        "scorecard_pointer": "reports/canonical/quality-scorecard.json:$.rows",
        "scorecard_hash": "fixture-hash",
        "scorecard_ready": True,
        "formal_hardening_ready": True,
    }


def _fixture_root(tmp_path: Path) -> Path:
    _write_json(
        tmp_path,
        "reports/canonical/gap-head-discovery.json",
        {
            "positive_discovery": True,
            "matched_random_control": {"status": "present"},
            "boundary_checks": {"forbidden_inference_columns": ["fixture"]},
            "final_main_claim_status": {"claim": "fixture"},
            "score_terms": {"status": "present"},
            "claim_capsule_ref": "reports/runs/gap-head-discovery/claim_capsule.json",
            **_positive_owner_contract("D4"),
        },
    )
    _write_json(
        tmp_path,
        "reports/runs/gap-head-discovery/claim_capsule.json",
        {"schema_id": "bedc.quality.claim_capsule", "what_was_learned": "fixture", "not_claimed": ["fixture"]},
    )
    _write_json(
        tmp_path,
        "reports/canonical/gap-head-transfer-atlas.json",
        {
            "multi_surface_d5_o": {"decision": "pass"},
            "config": {"control_arm": "matched_random_gap_head"},
            **_positive_owner_contract("D5-O"),
        },
    )
    discovery_rows = [
        {
            "report": "gap-head-discovery",
            "json_artifact": "reports/canonical/gap-head-discovery.json",
            "markdown_artifact": "reports/canonical/gap-head-discovery.md",
            "discovery_level": "D4",
            "terminal_verdict": "",
            "classifier_reasons": ["fixture"],
            "projection_status": "projected",
            "evidence_pointer": "$.positive_discovery",
            "audit_status": "valid",
            "audit_reason": "",
            "not_claimed": ["fixture"],
        },
        {
            "report": "gap-head-transfer-atlas",
            "json_artifact": "reports/canonical/gap-head-transfer-atlas.json",
            "markdown_artifact": "reports/canonical/gap-head-transfer-atlas.md",
            "discovery_level": "D5-O",
            "terminal_verdict": "projected_discovery_required",
            "classifier_reasons": ["fixture"],
            "projection_status": "projected",
            "evidence_pointer": "$.multi_surface_d5_o",
            "audit_status": "valid",
            "audit_reason": "",
            "mechanism_status": "blocked",
            "mechanism_pointer": "$.mechanism_evidence",
            "mechanism_ledger_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt.0.status",
        },
    ]
    _write_evidence_provenance_index(tmp_path, discovery_rows)
    _write_json(
        tmp_path,
        claim_graph.DISCOVERY_MAP_JSON_ARTIFACT,
        {"rows": discovery_rows},
    )
    _write_json(
        tmp_path,
        claim_graph.NEGATIVE_WITNESSES_JSON_ARTIFACT,
        {
            "witnesses": [
                {
                    "kind": "hidden_debt_positive",
                    "terminal_verdict": "demoted",
                    "terminal_reason": "audit-improvement-tradeoff",
                    "discovery_level": "DR",
                    "gate_basis": {"new_status": "audit-improvement-tradeoff"},
                }
            ]
        },
    )
    rows = [
        _row("claim:gap-head-discovery", "accepted_positive_discovery"),
        _row("claim:gap-head-transfer-atlas", "projected_discovery_required"),
        _row("claim:witness:hidden_debt_positive", "revoked_discovery"),
    ]
    rows[1]["source"] = "reports/canonical/gap-head-transfer-atlas.json:$.multi_surface_d5_o"
    rows[1]["ledger_pointer"] = "reports/canonical/discovery_map.json:$.rows[1].discovery_level"
    rows[2]["source"] = "reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]"
    rows[2]["ledger_pointer"] = "reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]"
    _write_jsonl(tmp_path, claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT, rows)
    _write_json(
        tmp_path,
        "reports/canonical/quality-scorecard.json",
        {
            "rows": [
                {"metric": metric, "status": "ready", "value": index}
                for index, metric in enumerate(canonical.QUALITY_SCORECARD_METRICS)
            ]
        },
    )
    _write_json(
        tmp_path,
        "reports/canonical/formal_hardening.json",
        {"ready": True, "recorded": 1, "required": 1, "gap_count": 0},
    )
    _write_json(
        tmp_path,
        "reports/canonical/gap_head_attribution_capsule.json",
        {
            "mechanism_evidence": {"mechanism_status": "blocked"},
            "ledger_debt": [{"status": "open"}],
        },
    )
    return tmp_path


def _payload(tmp_path: Path):
    return claim_graph.build_claim_graph_payload(root=_fixture_root(tmp_path), generated_at="2030-01-01T00:00:00+00:00")


def _errors(payload, root):
    rows = claim_graph.load_claim_verdict_rows(root)
    return claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows)


def _add_dgt_accepted_positive_fixture(root: Path) -> None:
    _write_dgt_owner_ref_fixtures(root)
    dgt_artifact = "reports/canonical/discovery-gated-transformer.json"
    dgt_payload = {
        "schema_id": "bedc-quality-lab:discovery-gated-transformer",
        "artifact_id": "bedc-quality-lab:discovery-gated-transformer",
        "generated_at": "2030-01-01T00:00:00+00:00",
        "producer": "scripts/run_discovery_gated_transformer.py",
        "projector": "bedc_quality_lab.discovery_gated_transformer.DiscoveryGatedTransformerProjector",
        "source_artifacts": {},
        "model_id": "discovery-gated-transformer",
        "architecture_spec": {"status": "present"},
        "claim_capsule_ref": "reports/runs/discovery-gated-transformer/claim_capsule.json",
        "d4_projection": {
            "discovery_level": "D4",
            "readiness": "ready",
            "matched_control": {"status": "present", "control_positive": False},
            "claim_basis": "bounded deterministic toy projection",
        },
        "d5_m_projection": {
            "status": "ready",
            "readiness": "ready",
            "discovery_level": "D5-M",
            "evidence_scope": ["bounded-design", "toy-model", "theorem-backed", "production-forbidden"],
            "terminal_verdict_scope": "Core",
            "not_claimed": [
                "Bounded D5-M mechanism claim over deterministic model-prototype evidence only.",
                "No production authority claim.",
                "No global superiority claim.",
                "No LLM replacement claim.",
                "No unbounded mechanism closure claim.",
            ],
        },
        "scaling_ladder": {
            "status": "ready",
            "review_status": "review-line-ready",
            "discovery_level": "D5-M",
            "not_claimed": [
                "Bounded model prototype scaling only.",
                "No production scale claim.",
                "No GPT or Llama claim.",
                "No global superiority claim.",
                "No LLM replacement claim.",
                "No universal recipe claim.",
                "No unbounded scaling law claim.",
            ],
        },
        "not_claimed": [
            "Bounded deterministic toy evidence only.",
            "No external operation authority.",
            "No universal training recipe claim.",
            "No external verdict ownership.",
        ],
        **_positive_owner_contract("D5-M"),
    }
    _write_json(
        root,
        dgt_artifact,
        dgt_payload,
    )
    _write_json(
        root,
        "reports/runs/discovery-gated-transformer/claim_capsule.json",
        {
            "schema_id": "bedc.quality.claim_capsule",
            "claim_status": "fixture",
            "not_claimed": ["bounded deterministic toy evidence only"],
            "what_was_learned": "fixture learned",
        },
    )
    _write_json(
        root,
        high_impact_review.MODEL_COMPARISON_ARTIFACT,
        {
            "status": "ready",
            "readiness": {"status": "ready", "failed_gates": []},
            "models": [
                {
                    "model_id": "dgt",
                    "metrics": {
                        "quality_q": {"status": "resolved", "value": 0.76},
                        "UER_reduction": {"status": "resolved", "value": 0.33},
                        "classifier_shift_count": {"status": "resolved", "value": 2.0},
                    },
                },
                {
                    "model_id": "base_transformer",
                    "metrics": {
                        "quality_q": {"status": "resolved", "value": 0.50},
                        "UER_reduction": {"status": "resolved", "value": 0.03},
                        "classifier_shift_count": {"status": "resolved", "value": 0.0},
                    },
                },
                {
                    "model_id": "matched_random_structural_control",
                    "metrics": {
                        "quality_q": {"status": "resolved", "value": 0.44},
                        "UER_reduction": {"status": "resolved", "value": 0.01},
                        "classifier_shift_count": {"status": "resolved", "value": 0.0},
                    },
                },
            ],
            "hardgates": {
                f"MC-HG{index}": {"status": "pass", "reason": "fixture"}
                for index in range(1, 11)
            },
        },
    )
    discovery_payload = json.loads((root / claim_graph.DISCOVERY_MAP_JSON_ARTIFACT).read_text(encoding="utf-8"))
    discovery_payload["rows"].append(
        {
            "report": "discovery-gated-transformer",
            "json_artifact": dgt_artifact,
            "markdown_artifact": "reports/canonical/discovery-gated-transformer.md",
            "discovery_level": "D5-M",
            "terminal_verdict": "",
            "classifier_reasons": ["fixture"],
            "projection_status": "projected",
            "evidence_pointer": "$.d5_m_projection",
            "control_pointer": "$.d4_projection.matched_control",
            "audit_status": "valid",
            "audit_reason": "",
            "not_claimed": list(dgt_payload["d5_m_projection"]["not_claimed"]),
        }
    )
    _write_evidence_provenance_index(
        root,
        discovery_payload["rows"],
        empirical_reports=("gap-head-discovery", "discovery-gated-transformer"),
    )
    _write_json(root, claim_graph.DISCOVERY_MAP_JSON_ARTIFACT, discovery_payload)
    rows = claim_graph.load_claim_verdict_rows(root)
    rows.append(_row("claim:discovery-gated-transformer", "projected_discovery_required"))
    rows[-1]["source"] = f"{dgt_artifact}:$.d5_m_projection"
    rows[-1]["ledger_pointer"] = f"{claim_graph.DISCOVERY_MAP_JSON_ARTIFACT}:$.rows[2].discovery_level"
    rows[-1]["claim_verdict"] = "accepted_positive_discovery"
    rows[-1]["reason"] = "positive-discovery-gates-pass"
    _write_jsonl(root, claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT, rows)
    _write_json(
        root,
        claim_graph.CLAIM_GRAPH_JSON_ARTIFACT,
        {
            "nodes": [
                {"node_id": "raw:discovery-gated-transformer", "node_type": "raw_evidence", "terminal_verdict": None},
                {
                    "node_id": "projected:discovery-gated-transformer",
                    "node_type": "projected_discovery",
                    "depends_on": ["raw:discovery-gated-transformer"],
                    "terminal_verdict": None,
                },
                {
                    "node_id": "terminal:discovery-gated-transformer",
                    "node_type": "terminal_claim",
                    "depends_on": ["projected:discovery-gated-transformer"],
                },
            ]
        },
    )
    _write_dgt_high_impact_review_pass(root)
    provisional_graph = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    _write_json(root, claim_graph.CLAIM_GRAPH_JSON_ARTIFACT, provisional_graph)


def test_claim_verdict_rows_have_terminal_graph_foreign_keys(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    nodes = payload["nodes"]
    terminal_ids = [node["node_id"] for node in nodes if node["node_type"] == "terminal_claim"]

    for row in claim_graph.load_claim_verdict_rows(root):
        assert row["claim_graph_node_id"] in terminal_ids
        assert terminal_ids.count(row["claim_graph_node_id"]) == 1


def test_claim_verdict_foreign_key_must_target_terminal_claim(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "terminal:gap-head-discovery":
            node["node_type"] = "projected_discovery"

    assert any("non-terminal" in error for error in _errors(broken, root))

    rows = claim_graph.load_claim_verdict_rows(root)
    rows[0]["claim_graph_node_id"] = "raw:gap-head-discovery"
    assert any("lacks terminal graph foreign key" in error for error in claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows))


def test_cg_hg4_non_claim_prefix_id_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    rows = claim_graph.load_claim_verdict_rows(root)
    rows[0]["claim_id"] = "raw:gap-head-discovery"

    with pytest.raises(ValueError, match="claim_id must start with claim: raw:gap-head-discovery"):
        claim_graph.terminal_node_id_for_claim_id(rows[0]["claim_id"])

    errors = claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows)
    assert any("claim_id must start with claim: raw:gap-head-discovery" in error for error in errors)

    _write_jsonl(root, claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT, rows)
    with pytest.raises(ValueError, match="claim_id must start with claim: raw:gap-head-discovery"):
        claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")


def test_terminal_claim_nodes_exact_cover_verdict_rows(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    broken["nodes"] = [node for node in broken["nodes"] if node["node_id"] != "terminal:gap-head-transfer-atlas"]

    assert any("exact cover mismatch" in error or "terminal node missing" in error for error in _errors(broken, root))


def test_terminal_exact_cover_rejects_extra_terminal_node(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    extra = deepcopy(next(node for node in payload["nodes"] if node["node_id"] == "terminal:gap-head-discovery"))
    extra["node_id"] = "terminal:extra-fixture"
    extra["source_pointer"] = f"{claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[0]"
    broken["nodes"].append(extra)

    assert any("exact cover mismatch" in error for error in _errors(broken, root))


def test_terminal_exact_cover_rejects_duplicate_foreign_key(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    rows = claim_graph.load_claim_verdict_rows(root)
    rows[1]["claim_graph_node_id"] = rows[0]["claim_graph_node_id"]

    errors = claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows)

    assert any("exact cover mismatch" in error for error in errors)


def test_terminal_claim_node_points_back_to_jsonl_line(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")

    by_id = {node["node_id"]: node for node in payload["nodes"]}
    node = by_id["terminal:gap-head-discovery"]
    assert node["source_pointer"] == "reports/canonical/claim_verdicts.jsonl:$.lines[0]"
    assert claim_graph.resolve_source_pointer(root, node["source_pointer"])["claim_id"] == "claim:gap-head-discovery"


def test_terminal_claim_verdict_matches_row_verdict(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "terminal:gap-head-discovery":
            node["terminal_verdict"] = "negative_discovery"

    assert any("terminal verdict mismatch" in error for error in _errors(broken, root))


def test_cg_hg1_accepted_positive_discovery_traces_to_raw_evidence(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "projected:gap-head-discovery":
            node["depends_on"] = []

    assert any("lacks raw_evidence ancestry" in error for error in _errors(broken, root))


def test_cg_hg2_d5_o_rows_record_mechanism_status(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    entries = payload["hardgates"]["CG-HG2"]["d5_o_mechanism"]

    assert entries
    assert entries[0]["projected_node_id"] == "projected:gap-head-transfer-atlas"
    assert entries[0]["mechanism_status"] == "blocked"
    assert entries[0]["mechanism_pointer"] == "$.mechanism_evidence"
    assert entries[0]["mechanism_source_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt.0.status"


def test_cg_hg3_raw_evidence_does_not_become_terminal_claim(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "terminal:gap-head-discovery":
            node["depends_on"] = ["raw:gap-head-discovery"]

    assert any("directly depends on raw_evidence" in error for error in _errors(broken, root))


def test_cg_hg5_all_source_pointers_resolve(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    broken["nodes"][0]["source_pointer"] = "reports/canonical/missing.json:$.x"

    assert any("source_pointer does not resolve" in error for error in _errors(broken, root))


def test_cg_hg6_dependency_cycle_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "projected:gap-head-discovery":
            node["depends_on"] = ["terminal:gap-head-discovery"]

    errors = _errors(broken, root)

    assert any("CG-HG6 dependency cycle" in error and "terminal:gap-head-discovery" in error for error in errors)


def test_cg_hg6_reports_revocation_nodes_as_separate_evidence(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    gate = payload["hardgates"]["CG-HG7"]
    nodes = payload["nodes"]

    assert gate["status"] == "pass"
    assert gate["node_count"] == len(nodes)
    assert gate["edge_count"] == sum(len(node["depends_on"]) for node in nodes)
    assert gate["revocation_node_ids"] == ["revocation:witness:hidden_debt_positive"]
    assert "revocation:witness:hidden_debt_positive" not in payload["hardgates"]["CG-HG1"]["terminal_ids"]


def test_cg_hg6_records_accepted_positive_evidence_gate(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    gate = payload["hardgates"]["CG-HG6"]

    assert gate["status"] == "pass"
    assert gate["criterion"] == "accepted positive terminals have acceptance evidence bundle"
    assert gate["terminal_ids"] == ["terminal:gap-head-discovery"]


def test_cg_hg6_catches_corrupt_positive_evidence_after_verdict_write(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    source_path = root / "reports/canonical/gap-head-discovery.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["boundary_checks"]["forbidden_inference_columns"] = []
    source_path.write_text(json.dumps(source, sort_keys=True) + "\n", encoding="utf-8")

    errors = _errors(payload, root)

    assert not any("CG-HG1" in error for error in errors)
    assert not any("CG-HG4" in error for error in errors)
    assert any("CG-HG6 positive-acceptance-evidence-missing:not_claimed" in error for error in errors)


def test_cg_hg6_ignores_non_accepted_rows(tmp_path):
    root = _fixture_root(tmp_path)
    rows = claim_graph.load_claim_verdict_rows(root)
    rows[0]["claim_verdict"] = "projected_positive_discovery"
    _write_jsonl(root, claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT, rows)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    source_path = root / "reports/canonical/gap-head-discovery.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["boundary_checks"]["forbidden_inference_columns"] = []
    source_path.write_text(json.dumps(source, sort_keys=True) + "\n", encoding="utf-8")

    assert claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows) == []


def test_dgt_accepted_positive_claim_graph_path_passes(tmp_path):
    root = _fixture_root(tmp_path)
    _add_dgt_accepted_positive_fixture(root)

    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    by_id = {node["node_id"]: node for node in payload["nodes"]}

    assert by_id["terminal:discovery-gated-transformer"]["depends_on"] == ("projected:discovery-gated-transformer",)
    assert by_id["projected:discovery-gated-transformer"]["depends_on"] == ("raw:discovery-gated-transformer",)
    assert by_id["projected:discovery-gated-transformer"]["evidence_scope"] == (
        "bounded-design",
        "toy-model",
        "theorem-backed",
        "production-forbidden",
    )
    assert by_id["raw:discovery-gated-transformer"]["terminal_verdict"] is None
    assert by_id["projected:discovery-gated-transformer"]["terminal_verdict"] is None
    assert _errors(payload, root) == []


def test_dgt_component_causal_claim_graph_requires_evidence_scope(tmp_path):
    root = _fixture_root(tmp_path)
    _add_dgt_accepted_positive_fixture(root)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "projected:discovery-gated-transformer":
            node["evidence_scope"] = None

    errors = _errors(broken, root)

    assert any("component-causal claim lacks evidence_scope" in error for error in errors)


@pytest.mark.parametrize(
    "evidence_scope",
    [
        [],
        ["bounded-design", "bounded-design"],
        ["bounded-design", "outside-enum"],
    ],
)
def test_dgt_component_causal_claim_graph_rejects_bad_evidence_scope(tmp_path, evidence_scope):
    root = _fixture_root(tmp_path)
    _add_dgt_accepted_positive_fixture(root)
    source_path = root / "reports/canonical/discovery-gated-transformer.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["d5_m_projection"]["evidence_scope"] = evidence_scope
    source_path.write_text(json.dumps(source, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="component-causal.*evidence_scope"):
        claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")


def test_dgt_component_causal_claim_graph_rejects_production_claim_with_forbidden_scope(tmp_path):
    root = _fixture_root(tmp_path)
    _add_dgt_accepted_positive_fixture(root)
    source_path = root / "reports/canonical/discovery-gated-transformer.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["d5_m_projection"]["terminal_verdict_scope"] = "production deployment authority"
    source_path.write_text(json.dumps(source, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="evidence_scope contradicts production claim"):
        claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")


def test_dgt_neural_ablation_pointer_absent_skips(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    rows = claim_graph.load_claim_verdict_rows(root)

    assert claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows) == []


def test_dgt_neural_ablation_pointer_present_validates_evidence_scope(tmp_path):
    root = _fixture_root(tmp_path)
    _write_json(
        root,
        "reports/canonical/dgt-neural-ablation.json",
        {
            "component_causal_claims": [
                {
                    "claim_id": "fixture",
                    "evidence_scope": ["bounded-design", "toy-model"],
                }
            ]
        },
    )
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    rows = claim_graph.load_claim_verdict_rows(root)

    assert claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows) == []

    source_path = root / "reports/canonical/dgt-neural-ablation.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["component_causal_claims"][0]["evidence_scope"] = ["bounded-design", "bounded-design"]
    source_path.write_text(json.dumps(source, sort_keys=True) + "\n", encoding="utf-8")

    errors = claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows)

    assert any("dgt-neural-ablation component_causal_claims[0] evidence_scope" in error for error in errors)


def test_dgt_accepted_positive_terminal_dependency_bypass_fails(tmp_path):
    root = _fixture_root(tmp_path)
    _add_dgt_accepted_positive_fixture(root)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "terminal:discovery-gated-transformer":
            node["depends_on"] = ["projected:gap-head-discovery"]

    errors = _errors(broken, root)

    assert any("DGT accepted-positive terminal must depend only on projected:DGT" in error for error in errors)


def test_dgt_accepted_positive_projected_dependency_mismatch_fails(tmp_path):
    root = _fixture_root(tmp_path)
    _add_dgt_accepted_positive_fixture(root)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "projected:discovery-gated-transformer":
            node["depends_on"] = ["raw:gap-head-discovery"]

    errors = _errors(broken, root)

    assert any("DGT accepted-positive projected node must depend only on raw:DGT" in error for error in errors)


@pytest.mark.parametrize("node_id", ["raw:discovery-gated-transformer", "projected:discovery-gated-transformer"])
def test_dgt_accepted_positive_raw_or_projected_terminal_verdict_leakage_fails(tmp_path, node_id):
    root = _fixture_root(tmp_path)
    _add_dgt_accepted_positive_fixture(root)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == node_id:
            node["terminal_verdict"] = "accepted_positive_discovery"

    errors = _errors(broken, root)

    assert any("DGT raw/projected nodes must not carry terminal verdict" in error for error in errors)


def test_terminal_claim_nodes_are_bijection_for_checked_in_verdict_rows():
    root = canonical.ROOT
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    verdict_rows = claim_graph.load_claim_verdict_rows(root)
    terminal_nodes = {
        node["node_id"]: node
        for node in payload["nodes"]
        if node["node_type"] == "terminal_claim"
        and str(node["source_pointer"]).startswith(f"{claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT}:")
    }

    assert set(terminal_nodes) == {row["claim_graph_node_id"] for row in verdict_rows}
    for index, row in enumerate(verdict_rows):
        node = terminal_nodes[row["claim_graph_node_id"]]
        assert node["source_pointer"] == f"{claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[{index}]"
        assert node["terminal_verdict"] == row["claim_verdict"]
        assert node["node_id"] == claim_graph.terminal_node_id_for_claim_id(row["claim_id"])


def test_accepted_positive_claim_fails_closed_without_owner_section(tmp_path):
    root = _fixture_root(tmp_path)
    index_path = root / "reports/canonical/index.json"
    index_payload = json.loads(index_path.read_text(encoding="utf-8"))
    index_payload.pop("evidence_provenance")
    index_path.write_text(json.dumps(index_payload, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="requires evidence provenance owner section"):
        claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")


def test_claim_graph_rejects_unresolvable_evidence_provenance_pointer(tmp_path):
    root = _fixture_root(tmp_path)
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    broken = deepcopy(payload)
    for node in broken["nodes"]:
        if node["node_id"] == "projected:gap-head-discovery":
            node["evidence_provenance_pointer"] = (
                "reports/canonical/index.json:$.evidence_provenance.discovery_rows[?report=gap-head-discovery]"
            )

    errors = claim_graph.validate_claim_graph_payload(broken, root=root)

    assert any("evidence_provenance_pointer does not resolve" in error for error in errors)


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
def test_claim_graph_discovery_map_loader_validates_committed_payload(tmp_path, mutate, message):
    root = _fixture_root(tmp_path)
    path = root / claim_graph.DISCOVERY_MAP_JSON_ARTIFACT
    payload = json.loads(path.read_text(encoding="utf-8"))
    mutate(payload["rows"][0])
    _write_json(root, claim_graph.DISCOVERY_MAP_JSON_ARTIFACT, payload)

    with pytest.raises(ValueError, match=message):
        claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")


def test_generated_claim_graph_preserves_terminal_ids(tmp_path, monkeypatch):
    rows = [
        {
            "report": "d4",
            "json_artifact": "reports/canonical/d4.json",
            "markdown_artifact": "reports/canonical/d4.md",
            "discovery_level": "D4",
            "terminal_verdict": "",
            "classifier_reasons": ["fixture"],
            "projection_status": "projected",
            "evidence_pointer": "$.positive_discovery",
            "audit_status": "valid",
            "audit_reason": "",
            "evidence_type": "empirical_training_clean",
            "evidence_provenance_pointer": evidence_provenance_pointer_for_report("d4"),
        }
    ]
    spec = canonical.CanonicalReportSpec(
        name="d4",
        command=("python3", "scripts/run_fixture.py"),
        json_artifact="reports/canonical/d4.json",
        markdown_artifact="reports/canonical/d4.md",
        required_json_keys=("source_artifacts",),
        estimated_seconds=1,
        bundle_role="hg_p_core",
        scope_pointer="$.scope",
        cost_pointer="$.cost",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive",
        control_pointer="$.control",
        no_control_rationale_pointer=None,
    )
    monkeypatch.setattr(claim_verdict_demo, "ROOT", tmp_path)
    monkeypatch.setattr(claim_verdict_demo, "CANONICAL_REPORTS", (spec,))
    _write_evidence_provenance_index(tmp_path, rows, empirical_reports=("d4",))
    _write_json(tmp_path, "reports/canonical/discovery_map.json", {"rows": rows})
    _write_json(tmp_path, "reports/canonical/quality-scorecard.json", {"rows": [{"metric": metric, "status": "ready"} for metric in canonical.QUALITY_SCORECARD_METRICS]})
    _write_json(tmp_path, "reports/canonical/formal_hardening.json", {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
    _write_json(tmp_path, "reports/canonical/discovery_negative_witnesses.json", {"witnesses": []})
    _write_json(
        tmp_path,
        "reports/canonical/d4.json",
            {
                "source_artifacts": {"cost_protocol": "configs/default_cost_protocol.yaml"},
                "scope": {"status": "present"},
                "cost": {"status": "present"},
                "not_claimed": ["fixture"],
                "positive": {"claim": "fixture"},
                "control": {"status": "present"},
                "positive_discovery": True,
                "net_information": 1.0,
                "net_positive_signal": True,
                "matched_random_control": {"control_verdict": {"positive": False}},
                **_positive_owner_contract("D4"),
            },
        )
    (tmp_path / "configs").mkdir(parents=True, exist_ok=True)
    (tmp_path / "configs/default_cost_protocol.yaml").write_text(
        (Path(__file__).resolve().parents[1] / "configs/default_cost_protocol.yaml").read_text(encoding="utf-8"),
        encoding="utf-8",
    )

    verdicts = claim_verdict_demo.write_claim_verdicts(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    payload = claim_graph.write_claim_graph(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert verdicts[0]["claim_graph_node_id"] == "terminal:d4"
    assert any(node["node_id"] == "terminal:d4" for node in payload["nodes"])


def test_index_reporting_hardgate_points_to_claim_graph_without_copying_topology():
    payload = json.loads((canonical.ROOT / "reports/canonical/index.json").read_text(encoding="utf-8"))
    forbidden = {"nodes", "edges", "topology", "terminal_claims"}

    for report in payload["reports"]:
        gate = report["discipline"]["reporting_hardgate"]
        cell = gate["cells"]["claim_graph_path"]
        assert set(cell) == {"pointer", "source_artifact", "status"}
        assert cell["source_artifact"] == canonical.CLAIM_GRAPH_JSON_ARTIFACT
        assert not (set(cell) & forbidden)


def test_cg_hg6_accepts_no_control_rationale_pointer(tmp_path, monkeypatch):
    rows = [
        {
            "report": "d4",
            "json_artifact": "reports/canonical/d4.json",
            "markdown_artifact": "reports/canonical/d4.md",
            "discovery_level": "D4",
            "terminal_verdict": "",
            "classifier_reasons": ["fixture"],
            "projection_status": "projected",
            "evidence_pointer": "$.positive_discovery",
            "audit_status": "valid",
            "audit_reason": "",
        }
    ]
    spec = canonical.CanonicalReportSpec(
        name="d4",
        command=("python3", "scripts/run_fixture.py"),
        json_artifact="reports/canonical/d4.json",
        markdown_artifact="reports/canonical/d4.md",
        required_json_keys=("source_artifacts",),
        estimated_seconds=1,
        bundle_role="hg_p_core",
        scope_pointer="$.scope",
        cost_pointer="$.cost",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive",
        control_pointer=None,
        no_control_rationale_pointer="$.no_control_rationale",
    )
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    monkeypatch.setattr(claim_verdict_demo, "ROOT", tmp_path)
    monkeypatch.setattr(claim_verdict_demo, "CANONICAL_REPORTS", (spec,))
    _write_evidence_provenance_index(tmp_path, rows, empirical_reports=("d4",))
    _write_json(tmp_path, "reports/canonical/discovery_map.json", {"rows": rows})
    _write_json(tmp_path, "reports/canonical/quality-scorecard.json", {"rows": [{"metric": metric, "status": "ready"} for metric in canonical.QUALITY_SCORECARD_METRICS]})
    _write_json(tmp_path, "reports/canonical/formal_hardening.json", {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
    _write_json(tmp_path, "reports/canonical/discovery_negative_witnesses.json", {"witnesses": []})
    _write_json(
        tmp_path,
        "reports/canonical/d4.json",
        {
            "source_artifacts": {"cost_protocol": "configs/default_cost_protocol.yaml"},
            "scope": {"status": "present"},
            "cost": {"status": "present"},
            "not_claimed": ["fixture"],
            "positive": {"claim": "fixture"},
            "no_control_rationale": {"reason": "fixture"},
            "claim_capsule_ref": "reports/runs/d4/claim_capsule.json",
            "positive_discovery": True,
            "net_information": 1.0,
            "net_positive_signal": True,
            "main_verdict": {
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
                "net_information": 1.0,
                "deltas": {"debt_delta": 0},
            },
            "evidence_basis": {
                "control_positive_discovery": False,
                "scorecard_ready": True,
                "audit_status": "valid",
            },
            "matched_random_control": {"control_verdict": {"positive": False}},
                "scope_seal": {
                    "status": "closed",
                    "toy": True,
                    "bounded": True,
                    "theorem": False,
                    "real_training": False,
                    "production_forbidden": True,
                },
                **_positive_owner_contract("D4"),
            },
        )
    _write_json(
        tmp_path,
        "reports/runs/d4/claim_capsule.json",
        {
            "schema_id": "bedc.quality.claim_capsule",
            "claim_status": "fixture",
            "not_claimed": ["fixture"],
            "what_was_learned": "fixture learned",
        },
    )
    (tmp_path / "configs").mkdir(parents=True, exist_ok=True)
    (tmp_path / "configs/default_cost_protocol.yaml").write_text(
        (Path(__file__).resolve().parents[1] / "configs/default_cost_protocol.yaml").read_text(encoding="utf-8"),
        encoding="utf-8",
    )

    verdicts = claim_verdict_demo.write_claim_verdicts(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    payload = claim_graph.write_claim_graph(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    errors = claim_graph.validate_claim_graph_payload(payload, root=tmp_path, claim_verdict_rows=verdicts)

    assert verdicts[0]["claim_verdict"] == "accepted_positive_discovery"
    assert payload["hardgates"]["CG-HG6"]["terminal_ids"] == ["terminal:d4"]
    assert errors == []

    source_path = tmp_path / "reports/canonical/d4.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["no_control_rationale"] = {}
    source_path.write_text(json.dumps(source, sort_keys=True) + "\n", encoding="utf-8")

    errors = claim_graph.validate_claim_graph_payload(payload, root=tmp_path, claim_verdict_rows=verdicts)

    assert any("CG-HG6 positive-acceptance-evidence-missing:control-or-no-control-rationale" in error for error in errors)


def test_cg_hg8_rejects_accepted_high_impact_terminal_without_review_pointer(tmp_path, monkeypatch):
    rows = [
        {
            "report": "d4",
            "json_artifact": "reports/canonical/d4.json",
            "markdown_artifact": "reports/canonical/d4.md",
            "discovery_level": "D4",
            "terminal_verdict": "",
            "classifier_reasons": ["fixture"],
            "projection_status": "projected",
            "evidence_pointer": "$.positive_discovery",
            "audit_status": "valid",
            "audit_reason": "",
        }
    ]
    spec = canonical.CanonicalReportSpec(
        name="d4",
        command=("python3", "scripts/run_fixture.py"),
        json_artifact="reports/canonical/d4.json",
        markdown_artifact="reports/canonical/d4.md",
        required_json_keys=("source_artifacts",),
        estimated_seconds=1,
        bundle_role="hg_p_core",
        scope_pointer="$.scope",
        cost_pointer="$.cost",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive",
        control_pointer="$.control",
        no_control_rationale_pointer=None,
    )
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    monkeypatch.setattr(claim_verdict_demo, "CANONICAL_REPORTS", (spec,))
    _write_evidence_provenance_index(tmp_path, rows, empirical_reports=("d4",))
    _write_json(tmp_path, "reports/canonical/discovery_map.json", {"rows": rows})
    _write_json(tmp_path, "reports/canonical/quality-scorecard.json", {"rows": [{"metric": metric, "status": "ready"} for metric in canonical.QUALITY_SCORECARD_METRICS]})
    _write_json(tmp_path, "reports/canonical/formal_hardening.json", {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
    _write_json(tmp_path, "reports/canonical/discovery_negative_witnesses.json", {"witnesses": []})
    _write_json(
        tmp_path,
        "reports/canonical/d4.json",
            {
                "source_artifacts": {"cost_protocol": "configs/default_cost_protocol.yaml"},
                "scope": {"status": "present"},
                "cost": {"status": "present"},
                "not_claimed": ["fixture"],
            "positive": {"claim": "bounded safety fixture"},
            "control": {"status": "present"},
                "claim_capsule_ref": "reports/runs/d4/claim_capsule.json",
                "positive_discovery": True,
                "net_information": 1.0,
                "net_positive_signal": True,
                **_positive_owner_contract("D4"),
            },
        )
    _write_json(
        tmp_path,
        "reports/runs/d4/claim_capsule.json",
        {
            "schema_id": "bedc.quality.claim_capsule",
            "claim_status": "fixture",
            "not_claimed": ["fixture"],
            "what_was_learned": "fixture learned",
        },
    )
    verdicts = [_row("claim:d4", "accepted_positive_discovery")]
    _write_jsonl(tmp_path, claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT, verdicts)

    with pytest.raises(ValueError) as excinfo:
        claim_graph.build_claim_graph_payload(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert "CG-HG8 high-impact-review-required: claim:d4 -> reports/canonical/d4.json:$.high_impact_claim_review" in str(excinfo.value)
