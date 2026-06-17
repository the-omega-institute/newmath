import json

from scripts import run_canonical_reports as canonical
from tests.test_fair_alignment_control_ledger import _write_source_payloads


def test_fair_alignment_control_ledger_canonical_spec_is_registered():
    spec = canonical._specs_by_name()["fair-alignment-control-ledger"]

    assert spec.command == ("python3", "scripts/run_fair_alignment_control_ledger.py")
    assert spec.json_artifact == "reports/canonical/fair-alignment-control-ledger.json"
    assert spec.markdown_artifact == "reports/canonical/fair-alignment-control-ledger.md"
    assert "rows" in spec.required_json_keys
    assert "hardgate" in spec.required_json_keys
    assert spec.positive_claim_pointer == "$.status"
    assert spec.control_pointer == "$.rows"
    assert spec.hardgate_status_pointer == "$.hardgate.status"


def test_fair_alignment_control_index_section_is_pointer_only():
    section = canonical._fair_alignment_control_ledger_index_section()

    assert section == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:fair-alignment-control-ledger",
        "json_artifact": "reports/canonical/fair-alignment-control-ledger.json",
        "markdown_artifact": "reports/canonical/fair-alignment-control-ledger.md",
        "rows_pointer": "reports/canonical/fair-alignment-control-ledger.json:$.rows",
        "hardgate_pointer": "reports/canonical/fair-alignment-control-ledger.json:$.hardgate",
        "producer_adapters_pointer": "reports/canonical/fair-alignment-control-ledger.json:$.producer_adapters",
    }


def test_fair_alignment_control_dispatch_writes_canonical_artifacts(monkeypatch, tmp_path):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    _write_source_payloads(tmp_path)
    spec = canonical._specs_by_name()["fair-alignment-control-ledger"]

    canonical._run_spec_producer(spec, generated_at="fixture-time")

    payload = json.loads((tmp_path / spec.json_artifact).read_text(encoding="utf-8"))
    markdown = (tmp_path / spec.markdown_artifact).read_text(encoding="utf-8")

    assert payload["generated_at"] == "fixture-time"
    assert payload["status"] == "pass"
    assert payload["hardgate"]["status"] == "pass"
    assert payload["row_count"] == 2
    assert payload["positive_claim"]["status"] == "positive-candidate"
    assert set(payload["producer_adapters"]) == {"gap-head-on-h", "discovery-regularized-training"}
    assert "- Generated at: `fixture-time`" in markdown
    assert "`pointer-only`" in markdown


def test_fair_alignment_control_targeted_selection_includes_source_reports():
    selected = canonical._selected_specs_with_dependents("fair-alignment-control-ledger")

    assert tuple(spec.name for spec in selected) == (
        "fair-alignment-control-ledger",
        "gap-head-on-h",
        "discovery-regularized-training",
    )


def test_sti_admission_dispatch_writes_canonical_artifacts(monkeypatch, tmp_path):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["sti-admission"]

    canonical._run_spec_producer(spec, generated_at="fixture-time")

    payload = json.loads((tmp_path / spec.json_artifact).read_text(encoding="utf-8"))
    markdown = (tmp_path / spec.markdown_artifact).read_text(encoding="utf-8")

    assert payload["generated_at"] == "fixture-time"
    assert payload["producer"] == "bedc_quality_lab.tasks.sti"
    assert payload["task_facts"]["owner"] == "bedc_quality_lab.tasks.sti"
    assert payload["verdict"] == "accepted"
    assert payload["hardgate"]["status"] == "pass"
    assert "- Downstream gate: `reports/canonical/sti-admission.json:$.downstream_gate`" in markdown
