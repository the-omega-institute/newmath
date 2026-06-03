import json

from bedc_quality_lab import claim_terms
from scripts import run_formal_hardening_report as formal_hardening


LEDGER_FIELDS = {
    "item_id",
    "name",
    "status",
    "recorded",
    "evidence_resolved",
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
    assert row["evidence_resolved"] is False
    assert row["required"] is True
    assert row["evidence_pointer"] is None
    assert row["gap"] == "delete-1 has no recorded finite ledger coverage evidence"
    assert payload["recorded"] == 3
    assert payload["required"] == 4
    assert payload["gap_count"] == 1
    assert payload["coverage"]["gap_rows"] == ["finite-ledger-coverage"]


def test_formal_hardening_report_fails_closed_for_bogus_pointer(monkeypatch):
    item = formal_hardening._HardeningItem(
        item_id="bogus-pointer",
        name="bogus pointer",
        row=formal_hardening.LedgerRowKey("formal-hardening", "bogus-pointer"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0]",
        evidence_pointer="reports/canonical/spectral-ablation-hinge.json:$.does_not_exist",
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))

    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    row = payload["verification_ledger"][0]

    assert row["status"] == "missing"
    assert row["recorded"] is False
    assert row["evidence_resolved"] is False
    assert payload["ready"] is False
    assert payload["coverage"]["ready"] is False


def test_formal_hardening_report_falsy_resolved_value_stays_missing(monkeypatch):
    evidence_pointer = "reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[2].recorded"
    item = formal_hardening._HardeningItem(
        item_id="falsy-pointer",
        name="falsy pointer",
        row=formal_hardening.LedgerRowKey("formal-hardening", "falsy-pointer"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[2]",
        evidence_pointer=evidence_pointer,
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))

    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    row = payload["verification_ledger"][0]

    assert row["status"] == "missing"
    assert row["recorded"] is False
    assert row["evidence_resolved"] is False
    assert payload["ready"] is False
    assert payload["coverage"]["ready"] is False


def test_formal_hardening_report_fails_closed_for_self_pointer(monkeypatch):
    item = formal_hardening._HardeningItem(
        item_id="self-pointer",
        name="self pointer",
        row=formal_hardening.LedgerRowKey("formal-hardening", "self-pointer"),
        source_pointer="reports/canonical/formal_hardening.json:$.verification_ledger",
        evidence_pointer="reports/canonical/formal_hardening.json:$.verification_ledger",
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))

    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    row = payload["verification_ledger"][0]

    assert row["status"] == "missing"
    assert row["recorded"] is False
    assert row["evidence_resolved"] is False
    assert payload["ready"] is False


def test_formal_hardening_report_fails_closed_for_missing_artifact(monkeypatch):
    item = formal_hardening._HardeningItem(
        item_id="missing-artifact",
        name="missing artifact",
        row=formal_hardening.LedgerRowKey("formal-hardening", "missing-artifact"),
        source_pointer="reports/canonical/missing-artifact.json:$.recorded",
        evidence_pointer="reports/canonical/missing-artifact.json:$.recorded",
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))

    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    row = payload["verification_ledger"][0]

    assert row["status"] == "missing"
    assert row["recorded"] is False
    assert row["evidence_resolved"] is False
    assert payload["ready"] is False


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
