import json

import pytest

from bedc_quality_lab import claim_terms
from bedc_quality_lab.discovery_compiler import capsule
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
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
    assert payload["status"] == "ready"
    assert payload["ready"] is True
    assert "schema_id" not in payload
    assert "report_schema_id" not in payload
    assert "report_kind" not in payload
    assert payload["verification_ledger"]
    assert all(set(row) == LEDGER_FIELDS for row in payload["verification_ledger"])
    assert {row["status"] for row in payload["verification_ledger"]} <= {"verified", "missing"}


def test_finite_ledger_coverage_has_resolved_lean_evidence_chain():
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    row = _row_by_id(payload)["finite-ledger-coverage"]

    assert row["status"] == "verified"
    assert row["recorded"] is True
    assert row["evidence_resolved"] is True
    assert row["required"] is True
    assert row["evidence_pointer"] == "lean://FiniteLedgerCoverage.coverage_of_recorded_witnesses"
    assert row["formal_pointer"] == "lean://FiniteLedgerCoverage.coverage_of_recorded_witnesses"
    assert row["gap"] is None
    assert "lab-local pointer-only finite coverage evidence" in row["trust_boundary"]
    assert "not a BEDC closure certificate" in row["trust_boundary"]
    assert "not a global model quality certificate" in row["trust_boundary"]
    assert payload["recorded"] == 4
    assert payload["required"] == 4
    assert payload["gap_count"] == 0
    assert payload["coverage"] == {
        "ready": True,
        "recorded": 4,
        "required": 4,
        "gap_count": 0,
        "gap_rows": [],
    }


def test_missing_row_negative_example_remains_independently_reportable():
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    row = _row_by_id(payload)["missing-row-negative-example"]
    lean_result = formal_hardening._resolve_evidence_pointer(
        "lean://FiniteLedgerCoverage.missingRow_not_covered",
        root=formal_hardening.ROOT,
    )

    assert row["status"] == "verified"
    assert row["recorded"] is True
    assert row["evidence_resolved"] is True
    assert row["item_id"] != "finite-ledger-coverage"
    assert lean_result.resolved is True
    assert lean_result.kind == "lean-symbol"
    assert lean_result.reason is None


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


def test_lean_evidence_pointer_resolves_for_tracked_theorem():
    result = formal_hardening._resolve_evidence_pointer(
        "lean://FiniteLedgerCoverage.coverage_of_recorded_witnesses",
        root=formal_hardening.ROOT,
    )

    assert result.resolved is True
    assert result.kind == "lean-symbol"
    assert result.reason is None


def test_lean_evidence_pointer_fails_closed_for_missing_symbol():
    result = formal_hardening._resolve_evidence_pointer(
        "lean://FiniteLedgerCoverage.missing_theorem",
        root=formal_hardening.ROOT,
    )

    assert result.resolved is False
    assert result.kind == "lean-symbol"
    assert result.reason == "missing Lean symbol"


def test_lean_evidence_pointer_fails_closed_for_missing_file(tmp_path):
    result = formal_hardening._resolve_evidence_pointer(
        "lean://FiniteLedgerCoverage.coverage_of_recorded_witnesses",
        root=tmp_path,
    )

    assert result.resolved is False
    assert result.kind == "lean-symbol"
    assert result.reason == "missing Lean file"


def test_lean_evidence_pointer_fails_closed_for_unknown_module():
    result = formal_hardening._resolve_evidence_pointer(
        "lean://UnknownModule.coverage_of_recorded_witnesses",
        root=formal_hardening.ROOT,
    )

    assert result.resolved is False
    assert result.kind == "lean-symbol"
    assert result.reason == "unknown Lean module"


@pytest.mark.parametrize(
    "pointer",
    [
        "lean:///tmp/FiniteLedgerCoverage.coverage_of_recorded_witnesses",
        "lean://../FiniteLedgerCoverage.coverage_of_recorded_witnesses",
        "lean://FiniteLedgerCoverage../coverage_of_recorded_witnesses",
        "/tmp/FiniteLedgerCoverage.lean:$.coverage",
        "file://formal/lean/FiniteLedgerCoverage.lean",
    ],
)
def test_evidence_pointer_fails_closed_for_path_like_or_traversal_shapes(pointer):
    result = formal_hardening._resolve_evidence_pointer(pointer, root=formal_hardening.ROOT)

    assert result.resolved is False
    assert result.kind in {"canonical-json", "invalid"}


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


def _generated_run_artifacts(root):
    run_dir = root / "reports" / "runs" / "formal-hardening-closure"
    return {
        "claim_capsule": run_dir / "claim_capsule.json",
        "raw_metrics": run_dir / "raw_metrics.jsonl",
        "summary": run_dir / "summary.json",
        "report": run_dir / "report.md",
    }


def _read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def _read_jsonl(path):
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def _recursive_keys(value):
    yield from _walk_keys(value)


def test_formal_hardening_claim_capsule_schema_contract(tmp_path):
    formal_hardening.write_formal_hardening_report(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    claim_capsule = _read_json(artifacts["claim_capsule"])
    raw_metrics = _read_jsonl(artifacts["raw_metrics"])
    summary = _read_json(artifacts["summary"])
    report = artifacts["report"].read_text(encoding="utf-8")

    assert claim_capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert claim_capsule["run_local"]
    for payload in (claim_capsule, raw_metrics, summary):
        assert "issue_schema_alias" not in set(_recursive_keys(payload))
    assert "issue_schema_alias" not in report


def test_formal_hardening_run_local_refs_resolve(tmp_path):
    formal_hardening.write_formal_hardening_report(root=tmp_path, generated_at="fixture-time")
    artifacts = _generated_run_artifacts(tmp_path)
    canonical = _read_json(tmp_path / "reports" / "canonical" / "formal_hardening.json")
    claim_capsule = _read_json(artifacts["claim_capsule"])
    raw_metrics = _read_jsonl(artifacts["raw_metrics"])
    run_local = claim_capsule["run_local"]

    assert run_local["source_artifact"] == "reports/canonical/formal_hardening.json"
    for pointer in (run_local["source_pointer"], run_local["ready_pointer"], run_local["ledger_pointer"]):
        assert pointer_value(canonical, pointer) is not None
    for row in raw_metrics:
        assert row["source_artifact"] == "reports/canonical/formal_hardening.json"
        assert pointer_value(canonical, row["source_pointer"]) is not None


def test_formal_hardening_summary_points_to_capsule_contract(tmp_path):
    formal_hardening.write_formal_hardening_report(root=tmp_path, generated_at="fixture-time")
    summary = _read_json(_generated_run_artifacts(tmp_path)["summary"])

    assert summary["claim_capsule_ref"] == {
        "artifact": "reports/runs/formal-hardening-closure/claim_capsule.json",
        "pointer": "$.run_local",
    }
    assert "run_local" not in summary


def test_formal_hardening_does_not_expand_capsule_schema_validator():
    assert capsule.CLAIM_CAPSULE_SCHEMA_ID == "bedc.quality.claim_capsule"
    assert capsule.CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID == "bedc.quality.claim_capsule.run_local"

    with pytest.raises(ValueError, match="claim capsule schema_id is invalid"):
        capsule.normalize_claim_capsule_schema_id(
            {
                "schema_id": "bedc.quality.claim_capsule.formal_hardening",
                "claim_id": "fixture",
                "report": "reports/runs/fixture/report.md",
                "source": "reports/canonical/formal_hardening.json",
                "source_pointer": "$.ready",
                "status": "complete",
            }
        )
