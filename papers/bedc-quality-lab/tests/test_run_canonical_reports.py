from scripts import run_canonical_reports as canonical


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
