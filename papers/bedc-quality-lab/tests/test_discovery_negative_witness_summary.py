import json
from pathlib import Path

import pytest

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_claim_verdict_demo as claim_verdicts
from scripts import run_discovery_map as discovery_map
from scripts import run_discovery_negative_witness_summary as summary
from bedc_quality_lab.discovery_compiler.negative_reports import OWNER_FACT_KEYS
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.discovery_compiler.projection import project_finite_discovery_gate
from bedc_quality_lab.discovery_compiler.claim_verdict_reason import (
    reason_basis_from_negative_owner,
    reason_for_claim_verdict,
)
from bedc_quality_lab.evidence_provenance import OWNER as EVIDENCE_PROVENANCE_OWNER
from bedc_quality_lab.evidence_provenance import SCHEMA_ID as EVIDENCE_PROVENANCE_SCHEMA_ID
from bedc_quality_lab.evidence_provenance import evidence_provenance_pointer_for_report


ALLOWED_ROW_KEYS = {
    "negative_id",
    "negative_verdict",
    "reason",
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


def _discovery_row_for_negative(row):
    return {
        "report": row["report"],
        "json_artifact": row["json_artifact"],
        "markdown_artifact": row["markdown_artifact"],
        "discovery_level": "DN",
        "projection_status": "projected",
        "evidence_pointer": row["evidence_pointer"],
        "audit_status": "valid",
        "audit_reason": "",
        "negative_report_pointer": "reports/canonical/negative_discovery_reports.json:$.rows[0]",
        "evidence_type": "boundary_negative",
        "evidence_provenance_pointer": evidence_provenance_pointer_for_report(str(row["report"])),
    }


def test_summary_covers_all_dn_discovery_map_rows():
    payload = _build_payload()
    discovery = _load_json(summary.ROOT / summary.DISCOVERY_MAP_ARTIFACT)
    dn_rows = [row for row in discovery["rows"] if row["discovery_level"] == "DN"]
    dn_summary = [row for row in payload["rows"] if row["negative_id"].startswith("dn:")]

    assert payload["audit_status"] == "pass"
    assert payload["dn_discovery_map_row_count"] == len(dn_rows)
    assert len(dn_summary) == len(dn_rows)
    expected_ids = {
        "dn:dimension-mismatch-scale-leakage"
        if row["report"] == "dimension-mismatch-debt-transfer"
        else f"dn:{row['report']}"
        for row in dn_rows
    }
    assert {row["negative_id"] for row in dn_summary} == expected_ids
    reports = _load_json(summary.ROOT / "reports/canonical/negative_discovery_reports.json")
    owners = {item["negative_id"]: item for item in reports["rows"]}
    for row in dn_summary:
        assert row["negative_verdict"] == "negative_discovery"
        owner = owners[row["negative_id"]]
        assert row["reason"] == reason_for_claim_verdict(
            reason_basis_from_negative_owner(owner, claim_verdict_pointer=row["claim_verdict_pointer"])
        )
        assert row["ledger_pointer"]
        assert row["discovery_map_pointer"].startswith("reports/canonical/discovery_map.json:$.rows[")
        assert row["discovery_map_pointer"].endswith(".negative_report_pointer")
        assert row["witness_pointer"] is None
        assert row["claim_verdict_pointer"].startswith("reports/canonical/claim_verdicts.jsonl:$.lines[")
        assert row["audit_status"] == "pass"


def test_summary_accepts_derivative_dn_as_pointer_only_negative_row(tmp_path):
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    negative_row = {
        "negative_id": "dn:transformer-derivative-atlas",
        "report_id": "transformer-derivative-atlas",
        "kind": "discovery_report",
        "report": "transformer-derivative-atlas",
        "claim_id": "claim:transformer-derivative-atlas",
        "source": "reports/canonical/transformer_derivative_atlas.json:$.hardgates.by_layer.layer_0.status",
        "json_artifact": "reports/canonical/transformer_derivative_atlas.json",
        "markdown_artifact": "reports/canonical/layerwise_jet_map.md",
        "ledger_pointer": "reports/canonical/transformer_derivative_atlas.json:$.ledger_gaps[0]",
        "discovery_level": "DN",
        "terminal_verdict": "negative_discovery",
        "classifier_reasons": ["verdict=rejected"],
        "projection_status": "projected",
        "evidence_pointer": "$.bounded_lab_evidence",
        "failed_gate": "$.hardgates.by_layer.layer_0.status",
        "debt_row_pointer": "$.ledger_gaps[0]",
        "audit_status": "pass",
        "audit_reason": "",
        "what_was_learned": "derivative hardgate failure remains ordinary debt evidence",
        "next_hypothesis": "close high-order instability before claiming mechanism-level derivative evidence",
        "discovery_map_pointer": None,
        "claim_verdict_pointer": None,
    }
    (canonical_dir / "negative_discovery_reports.json").write_text(
        json.dumps({"rows": [negative_row]}) + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "discovery_map.json").write_text(
        json.dumps(
            {
                "rows": [_discovery_row_for_negative(negative_row)]
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "claim_verdicts.jsonl").write_text(
        json.dumps(
            {
                "claim_id": "claim:transformer-derivative-atlas",
                "claim_verdict": "negative_discovery",
                "negative_report_pointer": "reports/canonical/negative_discovery_reports.json:$.rows[0]",
                "reason": "negative-discovery-failed-gate:hardgates-by-layer-layer-0-status",
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "discovery_negative_witnesses.json").write_text(
        json.dumps({"witnesses": []}) + "\n",
        encoding="utf-8",
    )

    payload = summary.build_discovery_negative_witness_summary(root=tmp_path, generated_at="fixture-time")

    assert payload["audit_status"] == "pass"
    assert payload["rows"] == [
        {
            "negative_id": "dn:transformer-derivative-atlas",
            "negative_verdict": "negative_discovery",
            "reason": "negative-discovery-failed-gate:hardgates-by-layer-layer-0-status",
            "ledger_pointer": "reports/canonical/transformer_derivative_atlas.json:$.ledger_gaps[0]",
            "discovery_map_pointer": "reports/canonical/discovery_map.json:$.rows[0].negative_report_pointer",
            "witness_pointer": None,
            "claim_verdict_pointer": "reports/canonical/claim_verdicts.jsonl:$.lines[0]",
            "audit_status": "pass",
        }
    ]


@pytest.mark.parametrize("index_payload", [{}, None])
def test_negative_witness_summary_ignores_missing_evidence_provenance_owner(tmp_path, index_payload):
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    negative_row = {
        "negative_id": "dn:transformer-derivative-atlas",
        "report_id": "transformer-derivative-atlas",
        "kind": "discovery_report",
        "report": "transformer-derivative-atlas",
        "claim_id": "claim:transformer-derivative-atlas",
        "source": "reports/canonical/transformer_derivative_atlas.json:$.hardgates.by_layer.layer_0.status",
        "json_artifact": "reports/canonical/transformer_derivative_atlas.json",
        "markdown_artifact": "reports/canonical/layerwise_jet_map.md",
        "ledger_pointer": "reports/canonical/transformer_derivative_atlas.json:$.ledger_gaps[0]",
        "discovery_level": "DN",
        "terminal_verdict": "negative_discovery",
        "classifier_reasons": ["verdict=rejected"],
        "projection_status": "projected",
        "evidence_pointer": "$.bounded_lab_evidence",
        "failed_gate": "$.hardgates.by_layer.layer_0.status",
        "debt_row_pointer": "$.ledger_gaps[0]",
        "audit_status": "pass",
        "audit_reason": "",
        "what_was_learned": "derivative hardgate failure remains ordinary debt evidence",
        "next_hypothesis": "close high-order instability before claiming mechanism-level derivative evidence",
        "discovery_map_pointer": None,
        "claim_verdict_pointer": None,
    }
    (canonical_dir / "negative_discovery_reports.json").write_text(json.dumps({"rows": [negative_row]}) + "\n", encoding="utf-8")
    (canonical_dir / "discovery_map.json").write_text(json.dumps({"rows": [_discovery_row_for_negative(negative_row)]}) + "\n", encoding="utf-8")
    (canonical_dir / "claim_verdicts.jsonl").write_text(
        json.dumps(
            {
                "claim_id": "claim:transformer-derivative-atlas",
                "claim_verdict": "negative_discovery",
                "negative_report_pointer": "reports/canonical/negative_discovery_reports.json:$.rows[0]",
                "reason": "negative-discovery-failed-gate:hardgates-by-layer-layer-0-status",
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "discovery_negative_witnesses.json").write_text(json.dumps({"witnesses": []}) + "\n", encoding="utf-8")
    if index_payload is not None:
        (canonical_dir / "index.json").write_text(json.dumps(index_payload) + "\n", encoding="utf-8")

    payload = summary.build_discovery_negative_witness_summary(root=tmp_path, generated_at="fixture-time")

    assert payload["audit_status"] == "pass"
    assert payload["rows"][0]["discovery_map_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].negative_report_pointer"


def test_negative_witness_summary_ignores_stale_evidence_provenance_owner(tmp_path):
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    negative_row = {
        "negative_id": "dn:transformer-derivative-atlas",
        "report_id": "transformer-derivative-atlas",
        "kind": "discovery_report",
        "report": "transformer-derivative-atlas",
        "claim_id": "claim:transformer-derivative-atlas",
        "source": "reports/canonical/transformer_derivative_atlas.json:$.hardgates.by_layer.layer_0.status",
        "json_artifact": "reports/canonical/transformer_derivative_atlas.json",
        "markdown_artifact": "reports/canonical/layerwise_jet_map.md",
        "ledger_pointer": "reports/canonical/transformer_derivative_atlas.json:$.ledger_gaps[0]",
        "discovery_level": "DN",
        "terminal_verdict": "negative_discovery",
        "classifier_reasons": ["verdict=rejected"],
        "projection_status": "projected",
        "evidence_pointer": "$.bounded_lab_evidence",
        "failed_gate": "$.hardgates.by_layer.layer_0.status",
        "debt_row_pointer": "$.ledger_gaps[0]",
        "audit_status": "pass",
        "audit_reason": "",
        "what_was_learned": "derivative hardgate failure remains ordinary debt evidence",
        "next_hypothesis": "close high-order instability before claiming mechanism-level derivative evidence",
        "discovery_map_pointer": None,
        "claim_verdict_pointer": None,
    }
    stale_owner_row = {
        "report": "transformer-derivative-atlas",
        "evidence_type": "deterministic_projection",
        "discovery_map_pointer": "reports/canonical/discovery_map.json:$.rows[0]",
        "metric_provenance_pointers": [],
        "producer_training_audit_pointer": None,
        "allowed_claim_kinds": ["projection_only"],
        "not_claimed": ["fixture owner cell is intentionally stale"],
    }
    (canonical_dir / "negative_discovery_reports.json").write_text(json.dumps({"rows": [negative_row]}) + "\n", encoding="utf-8")
    (canonical_dir / "discovery_map.json").write_text(json.dumps({"rows": [_discovery_row_for_negative(negative_row)]}) + "\n", encoding="utf-8")
    (canonical_dir / "claim_verdicts.jsonl").write_text(
        json.dumps(
            {
                "claim_id": "claim:transformer-derivative-atlas",
                "claim_verdict": "negative_discovery",
                "negative_report_pointer": "reports/canonical/negative_discovery_reports.json:$.rows[0]",
                "reason": "negative-discovery-failed-gate:hardgates-by-layer-layer-0-status",
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "discovery_negative_witnesses.json").write_text(json.dumps({"witnesses": []}) + "\n", encoding="utf-8")
    (canonical_dir / "index.json").write_text(
        json.dumps(
            {
                "evidence_provenance": {
                    "schema_id": EVIDENCE_PROVENANCE_SCHEMA_ID,
                    "owner": EVIDENCE_PROVENANCE_OWNER,
                    "generated_at": "fixture-time",
                    "producer_audits": [],
                    "metric_rows": [],
                    "discovery_rows": [stale_owner_row],
                    "discovery_rows_by_report": {"transformer-derivative-atlas": stale_owner_row},
                    "hardgate_status": {},
                    "artifact_pointers": {},
                }
            }
        )
        + "\n",
        encoding="utf-8",
    )

    payload = summary.build_discovery_negative_witness_summary(root=tmp_path, generated_at="fixture-time")

    assert payload["audit_status"] == "pass"
    assert payload["rows"][0]["discovery_map_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].negative_report_pointer"


def test_summary_fails_mismatched_claim_verdict_reason(tmp_path):
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    negative_row = {
        "negative_id": "dn:transformer-derivative-atlas",
        "report_id": "transformer-derivative-atlas",
        "kind": "discovery_report",
        "report": "transformer-derivative-atlas",
        "claim_id": "claim:transformer-derivative-atlas",
        "source": "reports/canonical/transformer_derivative_atlas.json:$.hardgates.by_layer.layer_0.status",
        "json_artifact": "reports/canonical/transformer_derivative_atlas.json",
        "markdown_artifact": "reports/canonical/layerwise_jet_map.md",
        "ledger_pointer": "reports/canonical/transformer_derivative_atlas.json:$.ledger_gaps[0]",
        "discovery_level": "DN",
        "terminal_verdict": "negative_discovery",
        "classifier_reasons": ["verdict=rejected"],
        "projection_status": "projected",
        "evidence_pointer": "$.bounded_lab_evidence",
        "failed_gate": "$.hardgates.by_layer.layer_0.status",
        "debt_row_pointer": "$.ledger_gaps[0]",
        "audit_status": "pass",
        "audit_reason": "",
        "what_was_learned": "derivative hardgate failure remains ordinary debt evidence",
        "next_hypothesis": "close high-order instability before claiming mechanism-level derivative evidence",
        "discovery_map_pointer": None,
        "claim_verdict_pointer": None,
    }
    (canonical_dir / "negative_discovery_reports.json").write_text(
        json.dumps({"rows": [negative_row]}) + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "discovery_map.json").write_text(
        json.dumps(
            {
                "rows": [_discovery_row_for_negative(negative_row)]
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "claim_verdicts.jsonl").write_text(
        json.dumps(
            {
                "claim_id": "claim:transformer-derivative-atlas",
                "claim_verdict": "negative_discovery",
                "negative_report_pointer": "reports/canonical/negative_discovery_reports.json:$.rows[0]",
                "reason": "negative-discovery-failed-gate:wrong-cell",
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "discovery_negative_witnesses.json").write_text(
        json.dumps({"witnesses": []}) + "\n",
        encoding="utf-8",
    )

    payload = summary.build_discovery_negative_witness_summary(root=tmp_path, generated_at="fixture-time")

    assert payload["audit_status"] == "fail"
    assert payload["audit_reasons"] == ["dn:transformer-derivative-atlas"]
    assert payload["rows"] == [
        {
            "negative_id": "dn:transformer-derivative-atlas",
            "negative_verdict": "negative_discovery",
            "reason": "negative-discovery-failed-gate:hardgates-by-layer-layer-0-status",
            "ledger_pointer": "reports/canonical/transformer_derivative_atlas.json:$.ledger_gaps[0]",
            "discovery_map_pointer": "reports/canonical/discovery_map.json:$.rows[0].negative_report_pointer",
            "witness_pointer": None,
            "claim_verdict_pointer": "reports/canonical/claim_verdicts.jsonl:$.lines[0]",
            "audit_status": "fail",
        }
    ]


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
        assert row["claim_verdict_pointer"].startswith("reports/canonical/claim_verdicts.jsonl:$.lines[")
        line_index_text = row["claim_verdict_pointer"].removeprefix("reports/canonical/claim_verdicts.jsonl:$.lines[")
        line_index_text = line_index_text.removesuffix("]")
        assert line_index_text.isdigit()
        compiled_row = compiled[int(line_index_text)]
        assert compiled_row["claim_id"] == f"claim:witness:{witness['kind']}"
        assert row["negative_verdict"] == compiled_row["claim_verdict"]
        assert row["reason"] == compiled_row["reason"]
        source = f"reports/canonical/discovery_negative_witnesses.json:$.witnesses[{index}]"
        assert row["ledger_pointer"] == source
        assert row["witness_pointer"] == source
        assert row["discovery_map_pointer"] is None
        assert row["audit_status"] == "pass"

    assert resolve_artifact_pointer(summary.ROOT, "reports/canonical/claim_verdicts.jsonl:0") == resolve_artifact_pointer(
        summary.ROOT,
        "reports/canonical/claim_verdicts.jsonl:$.lines[0]",
    )


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
            if key in {"ledger_pointer", "discovery_map_pointer", "witness_pointer", "claim_verdict_pointer"}:
                continue
            text = str(value).lower()
            assert not any(term in text for term in FORBIDDEN_POSITIVE_TERMS)


def test_finite_gate_consumes_negative_summary_row_pointers():
    payload = _build_payload()
    gate = project_finite_discovery_gate(
        {
            "discovery_map": _load_json(summary.ROOT / summary.DISCOVERY_MAP_ARTIFACT),
            "negative_witness_summary": payload,
        },
        root=summary.ROOT,
    )

    assert gate["hardgates"]["FG-HG2"]["status"] == "pass"
    assert gate["counts"]["negative"] == payload["row_count"]
    assert len(gate["pointers"]["negative"]) == payload["row_count"]
    assert gate["counts"]["negative_summary_report_rows"] == payload["dn_discovery_map_row_count"]
    assert gate["counts"]["negative_summary_witness_rows"] == payload["witness_row_count"]
    assert gate["counts"]["negative_summary_claim_verdict_rows"] == payload["claim_verdict_row_count"]
    for row in gate["pointers"]["negative"]:
        assert row[0]
        assert any(pointer for pointer in row[1:])
    forbidden_owner_terms = {"what_was_learned", "failed_gate", "hypothesis"}
    assert not any(term in json.dumps(gate, sort_keys=True) for term in forbidden_owner_terms)


def test_finite_gate_rejects_duplicate_negative_id_from_summary():
    payload = _build_payload()
    duplicate = {**payload, "rows": [*payload["rows"], dict(payload["rows"][0])], "row_count": payload["row_count"] + 1}
    gate = project_finite_discovery_gate(
        {
            "discovery_map": _load_json(summary.ROOT / summary.DISCOVERY_MAP_ARTIFACT),
            "negative_witness_summary": duplicate,
        },
        root=summary.ROOT,
    )

    assert gate["status"] == "fail"
    assert gate["hardgates"]["FG-HG2"]["status"] == "fail"
    assert "FG-HG2" in [name for name, hardgate in gate["hardgates"].items() if hardgate["status"] == "fail"]


def test_summary_rejects_owner_fact_keys_outside_pointers():
    payload = _build_payload()
    allowed_code_or_audit_keys = {"negative_id", "audit_status"}
    leaked_owner_keys = {
        key
        for row in payload["rows"]
        for key in row
        if key in OWNER_FACT_KEYS and not key.endswith("_pointer") and key not in allowed_code_or_audit_keys
    }

    assert leaked_owner_keys == set()


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
