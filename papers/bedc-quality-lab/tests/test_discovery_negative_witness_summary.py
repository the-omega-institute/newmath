import json
from pathlib import Path

import pytest

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_claim_verdict_demo as claim_verdicts
from scripts import run_discovery_map as discovery_map
from scripts import run_discovery_negative_witness_summary as summary


ALLOWED_ROW_KEYS = {
    "negative_id",
    "negative_verdict",
    "reason",
    "source",
    "ledger_pointer",
    "discovery_map_pointer",
    "witness_pointer",
    "claim_verdict_pointer",
    "audit_status",
}
FORBIDDEN_ROW_KEYS = {
    "gate_basis",
    "classifier_reasons",
    "discovery_reasons",
    "discovery_level",
    "score",
    "scores",
    "metrics",
    "metric",
    "grade",
    "level",
}
FORBIDDEN_POSITIVE_TERMS = {"full-lejepa", "global-quality", "full-tensor-namecert", "llm-behavior"}


def _load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def _build_payload():
    return summary.build_discovery_negative_witness_summary(
        root=summary.ROOT,
        generated_at="2030-01-01T00:00:00+00:00",
    )


def test_summary_covers_all_dn_discovery_map_rows():
    payload = _build_payload()
    discovery = _load_json(summary.ROOT / summary.DISCOVERY_MAP_ARTIFACT)
    dn_rows = [row for row in discovery["rows"] if row["discovery_level"] == "DN"]
    dn_summary = [row for row in payload["rows"] if row["negative_id"].startswith("dn:")]

    assert payload["audit_status"] == "pass"
    assert payload["dn_discovery_map_row_count"] == len(dn_rows)
    assert len(dn_summary) == len(dn_rows)
    assert {row["negative_id"] for row in dn_summary} == {f"dn:{row['report']}" for row in dn_rows}
    for row in dn_summary:
        assert row["negative_verdict"] == "negative_discovery"
        assert row["reason"] == "discovery-level-DN"
        assert row["ledger_pointer"]
        assert row["ledger_pointer"] == row["source"]
        assert row["discovery_map_pointer"].startswith("reports/canonical/discovery_map.json:$.rows[")
        assert row["witness_pointer"] is None
        assert row["claim_verdict_pointer"] is None
        assert row["audit_status"] == "pass"


def test_summary_covers_all_negative_witness_rows_with_compiled_verdict_pointers():
    payload = _build_payload()
    witnesses = _load_json(summary.ROOT / summary.NEGATIVE_WITNESSES_ARTIFACT)["witnesses"]
    compiled = claim_verdicts.compile_claim_verdicts(
        summary.ROOT,
        generated_at="2030-01-01T00:00:00+00:00",
    )
    witness_summary = [row for row in payload["rows"] if row["negative_id"].startswith("witness:")]

    assert payload["witness_row_count"] == len(witnesses)
    assert payload["claim_verdict_row_count"] == len(compiled)
    assert len(witness_summary) == len(witnesses)
    assert {row["negative_id"] for row in witness_summary} == {f"witness:{row['kind']}" for row in witnesses}
    for index, witness in enumerate(witnesses):
        row = next(item for item in witness_summary if item["negative_id"] == f"witness:{witness['kind']}")
        line_index_text = row["claim_verdict_pointer"].removeprefix("reports/canonical/claim_verdicts.jsonl:")
        assert line_index_text.isdigit()
        compiled_row = compiled[int(line_index_text)]
        assert compiled_row["claim_id"] == f"claim:witness:{witness['kind']}"
        assert row["negative_verdict"] == compiled_row["claim_verdict"]
        assert row["reason"] == compiled_row["reason"]
        assert row["source"] == f"reports/canonical/discovery_negative_witnesses.json:$.witnesses[{index}]"
        assert row["ledger_pointer"] == row["source"]
        assert row["witness_pointer"] == row["source"]
        assert row["discovery_map_pointer"] is None
        assert row["audit_status"] == "pass"


def test_summary_rows_are_pointer_only_and_key_allowlisted():
    payload = _build_payload()
    assert set(payload) == {
        "schema_id",
        "artifact_id",
        "generated_at",
        "status",
        "json_artifact",
        "markdown_artifact",
        "source_artifacts",
        "row_count",
        "dn_discovery_map_row_count",
        "witness_row_count",
        "claim_verdict_row_count",
        "audit_status",
        "audit_reasons",
        "rows",
    }
    assert payload["schema_id"] == "bedc-quality-lab:discovery-negative-witness-summary"
    assert payload["artifact_id"] == "bedc-quality-lab:discovery-negative-witness-summary"
    assert payload["status"] == "pointer-only"
    for row in payload["rows"]:
        assert set(row) == ALLOWED_ROW_KEYS
        assert not (set(row) & FORBIDDEN_ROW_KEYS)
        for key, value in row.items():
            if key in {"source", "ledger_pointer", "discovery_map_pointer", "witness_pointer", "claim_verdict_pointer"}:
                continue
            text = str(value).lower()
            assert not any(term in text for term in FORBIDDEN_POSITIVE_TERMS)


def test_summary_does_not_call_verdict_engine(monkeypatch):
    def fail_if_called(*_args, **_kwargs):
        raise AssertionError("summary producer must not call the verdict engine directly")

    monkeypatch.setattr("bedc_quality_lab.verdict.synthesize_certification_verdict", fail_if_called)
    monkeypatch.setattr(claim_verdicts, "synthesize_certification_verdict", fail_if_called)

    payload = summary.build_discovery_negative_witness_summary(
        root=summary.ROOT,
        generated_at="2030-01-01T00:00:00+00:00",
    )

    assert payload["audit_status"] == "pass"
    assert payload["dn_discovery_map_row_count"] >= 1
    witness_rows = [row for row in payload["rows"] if row["negative_id"].startswith("witness:")]
    assert witness_rows
    assert all(row["claim_verdict_pointer"] for row in witness_rows)


def test_summary_stays_outside_canonical_reports_and_preserves_schema_exports():
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    markdown_artifacts = {spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS}

    assert summary.JSON_ARTIFACT not in json_artifacts
    assert summary.MARKDOWN_ARTIFACT not in markdown_artifacts
    assert canonical.NEGATIVE_WITNESS_SUMMARY_JSON_ARTIFACT not in json_artifacts
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]


def test_canonical_index_contains_negative_witness_summary_section():
    payload = canonical._index([], generated_at="2030-01-01T00:00:00+00:00")
    section = payload["negative_witness_summary"]
    markdown = canonical._render_index_markdown(payload)

    assert section["status"] == "pointer-only"
    assert section["artifact_id"] == "bedc-quality-lab:discovery-negative-witness-summary"
    assert section["json_artifact"] == "reports/canonical/discovery_negative_witness_summary.json"
    assert section["markdown_artifact"] == "reports/canonical/discovery_negative_witness_summary.md"
    assert isinstance(section["row_count"], int)
    assert section["audit_status"] == "pass"
    assert "Negative witness summary" in markdown
    assert "discovery_negative_witness_summary.json" in markdown


def test_discovery_map_manifest_audit_accepts_summary_pointer_artifact():
    audit = discovery_map._manifest_audit(root=summary.ROOT)

    assert "reports/canonical/discovery_negative_witness_summary.json" not in audit["unregistered_json_artifacts"]
