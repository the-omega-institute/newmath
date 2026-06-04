import json
from copy import deepcopy
from pathlib import Path

import pytest

from bedc_quality_lab import claim_graph
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
        {"positive_discovery": True, "not_claimed": ["fixture"]},
    )
    _write_json(
        tmp_path,
        "reports/canonical/gap-head-transfer-atlas.json",
        {"multi_surface_d5_o": {"decision": "pass"}, "config": {"control_arm": "matched_random_gap_head"}},
    )
    _write_json(
        tmp_path,
        claim_graph.DISCOVERY_MAP_JSON_ARTIFACT,
        {
            "rows": [
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
                    "terminal_verdict": "ledger_only_hardening_not_ready",
                    "classifier_reasons": ["fixture"],
                    "projection_status": "projected",
                    "evidence_pointer": "$.multi_surface_d5_o",
                    "audit_status": "valid",
                    "audit_reason": "",
                },
            ]
        },
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
        _row("claim:gap-head-transfer-atlas", "ledger_only_hardening_not_ready"),
        _row("claim:witness:hidden_debt_positive", "demoted_audit_tradeoff"),
    ]
    rows[1]["source"] = "reports/canonical/gap-head-transfer-atlas.json:$.multi_surface_d5_o"
    rows[1]["ledger_pointer"] = "reports/canonical/discovery_map.json:$.rows[1].discovery_level"
    rows[2]["source"] = "reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]"
    rows[2]["ledger_pointer"] = "reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]"
    _write_jsonl(tmp_path, claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT, rows)
    _write_json(
        tmp_path,
        claim_graph.MECHANISM_NAMECERT_ARTIFACT,
        {"mechanism_spec": {"candidate_mechanism": "probe-margin-channel"}},
    )
    return tmp_path


def _payload(tmp_path: Path):
    return claim_graph.build_claim_graph_payload(root=_fixture_root(tmp_path), generated_at="2030-01-01T00:00:00+00:00")


def _errors(payload, root):
    rows = claim_graph.load_claim_verdict_rows(root)
    return claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows)


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
    assert entries[0]["mechanism_status"] == "no-d5-m-mechanism"


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


def test_terminal_claim_nodes_are_bijection_for_checked_in_verdict_rows():
    root = canonical.ROOT
    payload = claim_graph.build_claim_graph_payload(root=root, generated_at="2030-01-01T00:00:00+00:00")
    rows = claim_graph.load_claim_verdict_rows(root)
    row_ids = [row["claim_graph_node_id"] for row in rows]
    terminal_ids = [
        node["node_id"]
        for node in payload["nodes"]
        if node["node_type"] == "terminal_claim"
        and node["source_pointer"].startswith(f"{claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT}:")
    ]

    assert set(row_ids) == set(terminal_ids)
    assert len(row_ids) == len(terminal_ids)
    assert claim_graph.validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows) == []


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
