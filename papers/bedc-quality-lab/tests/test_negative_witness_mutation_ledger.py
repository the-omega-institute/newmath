import json

from bedc_quality_lab.backends.current_lab import projection
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer
from scripts import run_canonical_reports as canonical


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


def _cell(row, key):
    pointer = row[key]
    return f"{pointer['artifact']}:{pointer['pointer']}"


def test_negative_witness_mutation_ledger_exact_mapping():
    payload = canonical._negative_witness_mutation_ledger_payload(generated_at="fixture-time")
    rows = payload["rows"]

    assert payload["schema_id"] == canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_SCHEMA_ID
    assert payload["artifact_id"] == canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID
    assert payload["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert payload["row_count"] == 8
    assert {row["witness_id"]: row["mutation_target"] for row in rows} == EXPECTED_MAPPING
    assert payload["audit_status"] == "pass"


def test_negative_witness_mutation_ledger_rows_are_pointer_only_and_resolve():
    payload = canonical._negative_witness_mutation_ledger_payload(generated_at="fixture-time")
    forbidden = {
        "terminal_verdict",
        "discovery_level",
        "claim_id",
        "claim_verdict_pointer",
        "classifier_reasons",
        "what_was_learned",
        "next_hypothesis",
    }

    for row in payload["rows"]:
        assert forbidden.isdisjoint(row)
        assert row["audit_status"] == "pass"
        for key in (
            "source_witness_pointer",
            "mutation_target_pointer",
            "hardgate_pointer",
            "not_claimed_pointer",
        ):
            assert set(row[key]) == {"artifact", "pointer"}
            assert resolve_artifact_pointer(ROOT, _cell(row, key)) is not None


def test_negative_witness_mutation_ledger_blocks_dangling_pointer(monkeypatch):
    broken = {
        **canonical.NEGATIVE_WITNESS_MUTATION_ROWS[0],
        "source_witness_pointer": "reports/canonical/missing-negative-owner.json:$.rows[0]",
    }
    monkeypatch.setattr(canonical, "NEGATIVE_WITNESS_MUTATION_ROWS", (broken,))

    payload = canonical._negative_witness_mutation_ledger_payload(generated_at="fixture-time")

    assert payload["audit_status"] == "blocked"
    assert payload["blocked_witness_ids"] == ["score_margin_shortcut"]
    assert payload["rows"][0]["audit_status"] == "blocked"
    assert payload["rows"][0]["resolved_pointers"]["source_witness_pointer"] is False


def test_negative_witness_mutation_ledger_index_section_reads_written_payload(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    payload = {
        "artifact_id": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "row_count": 8,
        "audit_status": "pass",
    }
    artifact = tmp_path / canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT
    artifact.parent.mkdir(parents=True)
    artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")

    section = canonical._negative_witness_mutation_ledger_index_section()

    assert section == {
        "status": "pointer-only",
        "artifact_id": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID,
        "json_artifact": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT,
        "markdown_artifact": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_MARKDOWN_ARTIFACT,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "row_count": 8,
        "audit_status": "pass",
    }


def test_negative_witness_mutation_ledger_manifest_and_index_exposure():
    assert canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT not in {
        spec.json_artifact for spec in canonical.CANONICAL_REPORTS
    }
    assert (
        canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT
        not in projection._manifest_audit(root=ROOT)["unregistered_json_artifacts"]
    )

    index = json.loads((ROOT / "reports" / "canonical" / "index.json").read_text(encoding="utf-8"))
    section = index["negative_witness_mutation_ledger"]

    assert section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert section["json_artifact"] == canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT
    assert section["markdown_artifact"] == canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_MARKDOWN_ARTIFACT
    assert section["row_count"] == 8
    assert pointer_value(index, "$.negative_witness_mutation_ledger.audit_status") == "pass"
