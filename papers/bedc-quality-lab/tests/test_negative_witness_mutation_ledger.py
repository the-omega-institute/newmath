import json

from bedc_quality_lab.backends.current_lab import projection
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from scripts import run_canonical_reports as canonical
from scripts import run_negative_witness_mutation_ledger as ledger


ROOT = canonical.ROOT


EXPECTED_MAPPING = {
    "score_margin_shortcut": "residualized_h_path",
    "scale_leakage": "scale_invariant_norm",
    "control_positive": "control_separated_route",
    "benefit_debt_tradeoff": "constrained_lagrangian_loss",
    "single_threshold_escape": "threshold_frontier_loss",
    "forbidden_column": "inference_audit_layer",
    "hidden_debt": "explicit_ledger_head",
    "mechanism_blocked": "mechanism_seeking_module",
}

ENTRY_KEYS = {
    "mutation_id",
    "witness_kind",
    "source_artifact",
    "source_pointer",
    "target_module",
    "lineage_parent",
    "status",
    "reason",
}


def _source_cell(entry):
    return f"{entry['source_artifact']}:{entry['source_pointer']}"


def test_negative_witness_mutation_ledger_exact_mapping_and_schema():
    payload = ledger._build_mutation_ledger(ROOT, "fixture-time")
    entries = payload["entries"]

    assert payload["schema_id"] == ledger.LEDGER_SCHEMA_ID
    assert payload["artifact_id"] == ledger.LEDGER_ARTIFACT_ID
    assert payload["producer"] == ledger.PRODUCER
    assert payload["entry_count"] == 8
    assert {entry["witness_kind"]: entry["target_module"] for entry in entries} == EXPECTED_MAPPING
    assert all(set(entry) == ENTRY_KEYS for entry in entries)
    assert payload["status"] == "ready"
    assert {gate["status"] for gate in payload["hardgates"].values()} == {"pass"}


def test_negative_witness_mutation_ledger_pointers_resolve():
    payload = ledger._build_mutation_ledger(ROOT, "fixture-time")

    for index, entry in enumerate(payload["entries"]):
        assert ledger._resolve_artifact_pointer(ROOT, entry["source_artifact"], entry["source_pointer"]) is not None
        assert ledger._lineage_parent_resolves(ROOT, payload, entry, index)
        if index == 0:
            assert entry["lineage_parent"] == _source_cell(entry)
        else:
            assert entry["lineage_parent"] == f"{ledger.LEDGER_JSON_ARTIFACT}:$.entries[{index - 1}]"


def test_negative_witness_mutation_ledger_forbidden_keys_fail_closed():
    payload = ledger._build_mutation_ledger(ROOT, "fixture-time")
    payload["entries"][0]["terminal_verdict"] = "accepted"

    audit = ledger._audit_mutation_ledger(ROOT, payload)

    assert audit["status"] == "blocked"
    assert audit["hardgates"]["MUT-HG4"]["status"] == "fail"
    assert "$.entries[0].terminal_verdict" in audit["hardgates"]["MUT-HG4"]["hits"]


def test_negative_witness_mutation_ledger_blocks_dangling_source(monkeypatch):
    broken = {
        "witness_kind": "score_margin_shortcut",
        "source": "reports/canonical/missing-negative-owner.json:$.rows[0]",
        "target_module": "residualized_h_path",
    }
    monkeypatch.setattr(ledger, "_mutation_specs", lambda: (broken,))

    payload = ledger._build_mutation_ledger(ROOT, "fixture-time")

    assert payload["status"] == "blocked"
    assert payload["entries"][0]["status"] == "blocked"
    assert payload["hardgates"]["MUT-HG1"]["status"] == "fail"
    assert payload["hardgates"]["MUT-HG3"]["status"] == "fail"


def test_negative_witness_mutation_dgt_report_omits_entries_and_row_bodies():
    payload = ledger._build_mutation_ledger(ROOT, "fixture-time")
    report = ledger._build_dgt_mutation_report(payload)

    assert report["ledger"] == {"artifact": ledger.LEDGER_JSON_ARTIFACT, "pointer": "$.entries"}
    assert "entries" not in report
    assert "terminal_verdict" not in json.dumps(report, sort_keys=True)
    assert "source_pointer" not in json.dumps(report, sort_keys=True)


def test_negative_witness_mutation_graph_is_derived_from_ledger_pointers():
    payload = ledger._build_mutation_ledger(ROOT, "fixture-time")
    graph = ledger._render_lineage_graph(payload)

    assert f"{ledger.LEDGER_JSON_ARTIFACT}:$.entries" in graph
    for entry in payload["entries"]:
        assert entry["witness_kind"] in graph
        assert entry["target_module"] in graph
        assert _source_cell(entry) in graph
    assert "terminal_verdict" not in graph


def test_negative_witness_mutation_runner_round_trips_committed_json(tmp_path):
    payload = ledger.write_negative_witness_mutation_ledger(root=ROOT, generated_at="fixture-time")
    committed = json.loads((ROOT / ledger.LEDGER_JSON_ARTIFACT).read_text(encoding="utf-8"))
    dgt_report = json.loads((ROOT / ledger.DGT_REPORT_ARTIFACT).read_text(encoding="utf-8"))
    graph = (ROOT / ledger.LINEAGE_GRAPH_ARTIFACT).read_text(encoding="utf-8")

    assert committed == payload
    assert pointer_value(committed, "$.entries[0].witness_kind") == "score_margin_shortcut"
    assert dgt_report["ledger"] == {"artifact": ledger.LEDGER_JSON_ARTIFACT, "pointer": "$.entries"}
    assert "entries" not in dgt_report
    assert f"{ledger.LEDGER_JSON_ARTIFACT}:$.entries" in graph


def test_negative_witness_mutation_ledger_manifest_and_index_exposure():
    assert ledger.LEDGER_JSON_ARTIFACT not in {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    assert ledger.DGT_REPORT_ARTIFACT not in {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    assert (
        ledger.LEDGER_JSON_ARTIFACT
        not in projection._manifest_audit(root=ROOT)["unregistered_json_artifacts"]
    )

    section = canonical._negative_witness_mutation_ledger_index_section()

    assert section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert section["json_artifact"] == ledger.LEDGER_JSON_ARTIFACT
    assert section["graph_artifact"] == ledger.LINEAGE_GRAPH_ARTIFACT
    assert section["dgt_report_artifact"] == ledger.DGT_REPORT_ARTIFACT
    assert section["entry_count"] == 8
    assert section["entries_pointer"] == f"{ledger.LEDGER_JSON_ARTIFACT}:$.entries"
