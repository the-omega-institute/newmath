import json
from pathlib import Path

import pytest

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.research_discovery import assign_discovery_level
from scripts import run_canonical_reports as canonical
from tools import quality_discovery_adversarial_generator as generator
from tools import quality_discovery_gate_evolver as evolver


ROOT = Path(__file__).resolve().parents[1]
LEDGER_PATH = ROOT / generator.LEDGER_ARTIFACT
FORBIDDEN_LEDGER_FIELDS = {
    "schema_id",
    "report_schema_id",
    "report_kind",
    "SCHEMA_ID",
}


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def _checked_in_payload():
    return json.loads(LEDGER_PATH.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def runtime_by_kind():
    return {witness.kind: witness for witness in generator.runtime_witnesses()}


@pytest.fixture(scope="module")
def decisions_by_kind(runtime_by_kind):
    return {
        kind: generator._terminal_decision(witness)
        for kind, witness in runtime_by_kind.items()
    }


def _decision_for_kind(decisions_by_kind, kind):
    witness = decisions_by_kind[kind]
    return witness
    return generator._terminal_decision(witness)


def test_witness_ledger_has_exact_eight_kinds_and_soundness_fields():
    payload = _checked_in_payload()
    witnesses = payload["witnesses"]

    assert payload["artifact_id"] == "bedc-quality-lab:discovery-negative-witnesses"
    assert payload["status"] == "pointer-only"
    assert payload["expected_kind_count"] == 8
    assert [row["kind"] for row in witnesses] == list(generator.EXPECTED_KINDS)
    for row in witnesses:
        assert isinstance(row["soundness"], str)
        assert row["soundness"].strip()


def test_witness_ledger_stays_outside_report_and_scorecard_schema_boundary():
    payload = _checked_in_payload()
    keys = set(_walk_keys(payload))
    text = json.dumps(payload, sort_keys=True)

    assert keys.isdisjoint(FORBIDDEN_LEDGER_FIELDS)
    assert "host.env" not in text
    assert "QualityEvidenceEnvelope" not in text
    assert "quality_scorecard" not in keys
    assert "scorecard" not in keys


@pytest.mark.parametrize("kind", generator.EXPECTED_KINDS)
def test_each_pseudo_witness_fails_closed_under_current_verdict_gate(decisions_by_kind, kind):
    decision = _decision_for_kind(decisions_by_kind, kind)
    projected = assign_discovery_level(decision)

    assert decision["verdict"] in {"rejected", "demoted", "ledger-only"}
    assert decision["verdict"] != "positive-discovery"
    assert projected.discovery_level not in {"D4", "D5-O", "D5-M"}


def test_cost_protocol_missing_and_scorecard_not_ready_never_reach_positive_levels(decisions_by_kind):
    cost = _decision_for_kind(decisions_by_kind, "cost_protocol_missing")
    scorecard = _decision_for_kind(decisions_by_kind, "scorecard_not_ready")

    assert cost["verdict"] in {"rejected", "ledger-only"}
    assert assign_discovery_level(cost).discovery_level not in {"D4", "D5-O", "D5-M"}
    assert scorecard["verdict"] in {"rejected", "ledger-only"}
    assert assign_discovery_level(scorecard).discovery_level not in {"D4", "D5-O", "D5-M"}


def test_replay_matches_checked_in_pointer_only_ledger():
    replayed = generator.replay_checked_in_ledger(LEDGER_PATH)

    assert replayed == _checked_in_payload()


def test_generator_and_evolver_refresh_write_scope_is_allowlisted(tmp_path, monkeypatch):
    monkeypatch.setattr(generator, "ROOT", tmp_path)
    monkeypatch.setattr(evolver, "ROOT", tmp_path)
    target = tmp_path / generator.LEDGER_ARTIFACT
    writes = []

    def fake_replace(self, destination):
        writes.append(Path(destination).resolve())

    monkeypatch.setattr(Path, "replace", fake_replace)
    generator.write_witness_ledger(target, generated_at="2026-06-03T00:00:00+00:00")

    assert writes == [target.resolve()]
    with pytest.raises(ValueError):
        generator.write_witness_ledger(tmp_path / "other.json")

    calls = []

    def fake_write(path):
        calls.append(path.resolve())
        return {"witnesses": [{"kind": kind} for kind in generator.EXPECTED_KINDS]}

    monkeypatch.setattr(evolver, "write_witness_ledger", fake_write)
    evolver.main(["--refresh"])

    assert calls == [target.resolve()]


def test_pointer_glue_is_pointer_only_and_not_in_canonical_reports():
    reports = [
        {
            "name": spec.name,
            "bundle_role": spec.bundle_role,
            "status": "pass",
            "json_artifact": spec.json_artifact,
            "markdown_artifact": spec.markdown_artifact,
            "discipline": {
                "scope_pointer": spec.scope_pointer,
                "cost_pointer": spec.cost_pointer,
                "not_claimed_pointer": spec.not_claimed_pointer,
                "positive_claim_pointer": spec.positive_claim_pointer,
                "control_pointer": spec.control_pointer,
                "no_control_rationale_pointer": spec.no_control_rationale_pointer,
            },
        }
        for spec in canonical.CANONICAL_REPORTS
    ]
    payload = canonical._index(reports, generated_at="2026-06-03T00:00:00+00:00")
    section = payload["negative_witnesses"]

    assert section == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:discovery-negative-witnesses",
        "json_artifact": "reports/canonical/discovery_negative_witnesses.json",
        "expected_kind_count": 8,
    }
    assert "discovery_negative_witnesses.json" not in {
        Path(spec.json_artifact).name for spec in canonical.CANONICAL_REPORTS
    }


def test_forbidden_overclaim_witness_uses_claim_terms_as_only_term_source(runtime_by_kind, decisions_by_kind):
    witness = runtime_by_kind["forbidden_inference_column"]
    decision = decisions_by_kind["forbidden_inference_column"]

    assert witness.certificate_payload["positive_claim_cell"]["term_source"] == (
        "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS"
    )
    assert decision["evidence_basis"]["forbidden_claim_term_hits"] == [FORBIDDEN_POSITIVE_CLAIM_TERMS[0]]
