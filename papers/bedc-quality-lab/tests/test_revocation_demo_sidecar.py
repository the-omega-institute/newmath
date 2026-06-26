import json
from pathlib import Path

import pytest

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_revocation_demo_sidecar as sidecar


def _source_payload():
    return sidecar.load_source(Path("."))


def _payload():
    return sidecar.build_payload(_source_payload())


def test_sidecar_projects_current_no_certified_claim_case_from_canonical_pointer():
    source = _source_payload()
    payload = sidecar.build_payload(source)
    current = payload["transition_cases"][0]

    assert current["case_id"] == "current-no-certified-claim"
    assert current["decision"] == source["revocation_decision"]
    assert current["ledger_rows"] == source["revocation_ledger"]
    assert current["source_pointers"]["decision"].endswith("#$.revocation_decision")
    assert current["expected_predicates"] == {
        "downgraded": False,
        "reason": "no-certified-claim",
        "ledger_rows": 0,
    }


def test_sidecar_generates_synthetic_tradeoff_downgrade_with_demo_boundary(monkeypatch):
    calls = []
    original = sidecar.reevaluate_certified_claim

    def wrapped(certificate_payload, fresh_projection, *, timestamp_iso):
        calls.append(certificate_payload)
        return original(certificate_payload, fresh_projection, timestamp_iso=timestamp_iso)

    monkeypatch.setattr(sidecar, "reevaluate_certified_claim", wrapped)
    payload = _payload()
    synthetic = payload["transition_cases"][1]

    assert len(calls) == 1
    assert calls[0]["main_claim_status"] == "positive"
    assert synthetic["demo_only"] is True
    assert synthetic["synthetic_certificate"] is True
    assert synthetic["not_scientific_result"] is True
    assert synthetic["decision"]["downgraded"] is True
    assert synthetic["decision"]["new_status"] == "audit-improvement-tradeoff"
    assert synthetic["ledger_rows"][0]["event"] == "certified-claim-revocation"


def test_sidecar_is_not_canonical_or_shared_schema(tmp_path):
    payload = _payload()
    sidecar.write_artifacts(payload, root=tmp_path)
    written = json.loads((tmp_path / sidecar.JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert written["schema_id"] == sidecar.LOCAL_SCHEMA_ID
    assert written["schema_id"] != SCHEMA_ID
    assert written["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert not hasattr(bedc_quality_lab.QualityEvidenceEnvelope, "SCHEMA_ID")
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert sidecar.JSON_ARTIFACT not in [spec.json_artifact for spec in canonical.CANONICAL_REPORTS]


def test_sidecar_markdown_has_two_cell_table_and_not_claimed_boundary():
    markdown = sidecar.render_markdown(_payload())

    assert "| `current-no-certified-claim` |" in markdown
    assert "| `synthetic-old-positive-tradeoff` |" in markdown
    assert sum(1 for line in markdown.splitlines() if line.startswith("| `")) == 2
    assert "Not-Claimed Boundary" in markdown
    assert "current canonical run has no real downgrade" in markdown
    lower = markdown.lower()
    for term in ("full-lejepa", "global-quality", "full-tensor-namecert", "llm-behavior"):
        assert term not in lower


def test_sidecar_fails_closed_on_missing_source_keys(tmp_path):
    source_dir = tmp_path / "reports" / "canonical"
    source_dir.mkdir(parents=True)
    source = _source_payload()
    source.pop("revocation_decision")
    (source_dir / "certificate-guided-discovery.json").write_text(
        json.dumps(source),
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="revocation_decision"):
        sidecar.load_source(tmp_path)
