import json

from bedc_quality_lab import claim_terms
from scripts import run_formal_hardening_report as formal_hardening


LEDGER_FIELDS = {
    "item_id",
    "name",
    "status",
    "recorded",
    "required",
    "source_pointer",
    "evidence_pointer",
    "formal_pointer",
    "gap",
    "trust_boundary",
}


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def _row_by_id(payload):
    return {row["item_id"]: row for row in payload["verification_ledger"]}


def test_formal_hardening_report_has_pointer_only_ledger_schema():
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")

    assert payload["artifact_id"] == "bedc-quality-lab:formal-hardening"
    assert payload["producer"] == "scripts/run_formal_hardening_report.py"
    assert payload["status"] == "not-ready"
    assert payload["ready"] is False
    assert "schema_id" not in payload
    assert "report_schema_id" not in payload
    assert "report_kind" not in payload
    assert payload["verification_ledger"]
    assert all(set(row) == LEDGER_FIELDS for row in payload["verification_ledger"])
    assert {row["status"] for row in payload["verification_ledger"]} <= {"verified", "missing"}


def test_delete_1_finite_ledger_coverage_is_currently_missing():
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    row = _row_by_id(payload)["finite-ledger-coverage"]

    assert row["status"] == "missing"
    assert row["recorded"] is False
    assert row["required"] is True
    assert row["evidence_pointer"] is None
    assert row["gap"] == "delete-1 has no recorded finite ledger coverage evidence"
    assert payload["recorded"] == 3
    assert payload["required"] == 4
    assert payload["gap_count"] == 1
    assert payload["coverage"]["gap_rows"] == ["finite-ledger-coverage"]


def test_formal_hardening_report_has_no_forbidden_claim_or_hidden_weight_terms():
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    markdown = formal_hardening.render_markdown(payload)
    blob = json.dumps(payload).lower() + "\n" + markdown.lower()

    for term in claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS:
        assert term not in blob
    keys = set(_walk_keys(payload))
    assert "score" not in keys
    assert "weight" not in keys
    assert "weighted_total" not in keys
    assert "grade" not in keys


def test_write_formal_hardening_report_writes_json_and_markdown(tmp_path):
    payload = formal_hardening.write_formal_hardening_report(root=tmp_path, generated_at="fixture-time")

    json_path = tmp_path / "reports" / "canonical" / "formal_hardening.json"
    markdown_path = tmp_path / "reports" / "canonical" / "formal_hardening.md"
    assert json_path.exists()
    assert markdown_path.exists()
    assert json.loads(json_path.read_text(encoding="utf-8")) == payload
    assert "finite-ledger-coverage" in markdown_path.read_text(encoding="utf-8")
