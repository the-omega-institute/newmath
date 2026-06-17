import json
from pathlib import Path

from bedc_quality_lab import aggregation_consistency as agg
from bedc_quality_lab import claim_graph
from tests.test_claim_graph import _fixture_root, _write_json, _write_jsonl


def _phrase(*parts: str) -> str:
    return "".join(parts)


def _write_index(root: Path, *, generated_at: str = "2030-01-01T00:00:00+00:00") -> dict[str, object]:
    scorecard_rows = json.loads((root / agg.QUALITY_SCORECARD_ARTIFACT).read_text(encoding="utf-8"))["rows"]
    discovery_rows = json.loads((root / agg.DISCOVERY_MAP_ARTIFACT).read_text(encoding="utf-8"))["rows"]
    claim_rows = claim_graph.load_claim_verdict_rows(root)
    graph = claim_graph.build_claim_graph_payload(root=root, generated_at=generated_at)
    _write_json(root, claim_graph.CLAIM_GRAPH_JSON_ARTIFACT, graph)
    _write_json(
        root,
        agg.NEGATIVE_WITNESS_SUMMARY_ARTIFACT,
        {
            "generated_at": generated_at,
            "row_count": 1,
            "rows": [{"claim_verdict_pointer": f"{claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[2]"}],
        },
    )
    payload = {
        "schema_id": "bedc-quality-lab:canonical-report-index",
        "generated_at": generated_at,
        "quality_scorecard": {"status": "pointer-only", "metric_count": len(scorecard_rows)},
        "discovery_map": {"status": "pointer-only", "row_count": len(discovery_rows)},
        "claim_verdicts": {"status": "pointer-only", "row_count": len(claim_rows)},
        "claim_graph": {"status": "pointer-only", "node_count": graph["node_count"]},
        "negative_witness_summary": {"status": "pointer-only", "row_count": 1},
    }
    _write_json(root, agg.INDEX_ARTIFACT, payload)
    return payload


def _valid_root(tmp_path: Path) -> Path:
    root = _fixture_root(tmp_path)
    _write_index(root)
    return root


def _errors(root: Path, index_payload=None):
    return agg.validate_aggregation_consistency(root, index_payload=index_payload).errors


def test_agg_hg1_detects_claim_verdict_line_drift(tmp_path):
    root = _valid_root(tmp_path)
    graph = json.loads((root / claim_graph.CLAIM_GRAPH_JSON_ARTIFACT).read_text(encoding="utf-8"))
    for node in graph["nodes"]:
        if node["node_id"] == "terminal:gap-head-discovery":
            node["terminal_verdict"] = "negative_discovery"
    _write_json(root, claim_graph.CLAIM_GRAPH_JSON_ARTIFACT, graph)

    errors = _errors(root)

    assert any("AGG-HG1 projection mismatch" in error for error in errors)


def test_agg_hg2_detects_owner_newer_than_index(tmp_path):
    root = _valid_root(tmp_path)
    payload = json.loads((root / agg.DISCOVERY_MAP_ARTIFACT).read_text(encoding="utf-8"))
    payload["generated_at"] = "2031-01-01T00:00:00+00:00"
    _write_json(root, agg.DISCOVERY_MAP_ARTIFACT, payload)

    errors = _errors(root)

    assert any("AGG-HG2 owner newer than index" in error for error in errors)


def test_agg_hg3_detects_terminal_source_pointer_flip_without_regen(tmp_path):
    root = _valid_root(tmp_path)
    graph = json.loads((root / claim_graph.CLAIM_GRAPH_JSON_ARTIFACT).read_text(encoding="utf-8"))
    for node in graph["nodes"]:
        if node["node_id"] == "terminal:gap-head-discovery":
            node["source_pointer"] = f"{claim_graph.CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[1]"
    _write_json(root, claim_graph.CLAIM_GRAPH_JSON_ARTIFACT, graph)

    errors = _errors(root)

    assert any("terminal projection verdict mismatch" in error for error in errors)


def test_agg_hg4_rejects_aggregate_owned_verdict_injection(tmp_path):
    root = _valid_root(tmp_path)
    index_payload = json.loads((root / agg.INDEX_ARTIFACT).read_text(encoding="utf-8"))
    index_payload["claim_verdicts"]["terminal_verdict"] = "accepted_positive_discovery"

    errors = _errors(root, index_payload=index_payload)

    assert any("AGG-HG4 aggregate-owned verdict field" in error for error in errors)


def test_doc_hg_forbidden_phrase_without_boundary_pointer_fails(tmp_path):
    path = tmp_path / "doc.md"
    path.write_text(_phrase("DGT 已有训练", "实证优于 Transformer\n"), encoding="utf-8")

    report = agg.scan_doc_hg_surfaces(tmp_path, paths=[path])

    assert report.hardgates["DOC-HG"] == "fail"
    assert any("DOC-HG forbidden phrase" in error for error in report.errors)


def test_doc_hg_boundary_pointer_allows_phrase(tmp_path):
    path = tmp_path / "doc.md"
    path.write_text(
        "Correction pointer: `reports/canonical/index.json:$.honest_boundary.not_claimed`\n"
        + _phrase("DGT 已有训练", "实证优于 Transformer\n"),
        encoding="utf-8",
    )

    report = agg.scan_doc_hg_surfaces(tmp_path, paths=[path])

    assert report.errors == []


def test_doc_hg_correction_pointer_allows_phrase(tmp_path):
    path = tmp_path / "doc.md"
    path.write_text(
        "Correction pointer: `reports/canonical/claim_graph.json:$.hardgates.CG-HG4`\n"
        + _phrase("base_transformer", "_l1\n"),
        encoding="utf-8",
    )

    report = agg.scan_doc_hg_surfaces(tmp_path, paths=[path])

    assert report.errors == []


def test_doc_hg_scans_default_surfaces_when_present(tmp_path):
    surface = tmp_path / "reports/canonical/scaling-ladder.md"
    surface.parent.mkdir(parents=True, exist_ok=True)
    surface.write_text(_phrase("L1 scaling ", "成功\n"), encoding="utf-8")

    report = agg.scan_doc_hg_surfaces(tmp_path)

    assert report.doc_scan_count == 1
    assert any("scaling-ladder.md" in error for error in report.errors)
