import json
from pathlib import Path
import subprocess
import sys

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
EXPECTED_GAP_FIELDS = {
    "classifier_surface_delta_zero": "ClassifierSpec gap",
    "matched_control_positive": "Control / Intervention ledger gap",
    "hidden_debt_positive": "LedgerPolicy gap",
    "cost_protocol_missing": "CostProtocol gap",
    "scorecard_not_ready": "ClosureStatus gap",
    "forbidden_inference_column": "SourceSpec contamination",
    "benefit_debt_tradeoff": "Positive information gap",
    "fresh_claim_downgrade": "Revocation ledger gap",
    "synthetic_leakage_injection": "SourceSpec contamination",
}
FORBIDDEN_REGRESSION_POINTER_TERMS = ("count", "import", "wrapper")
POSITIVE_DISCOVERY_LEVELS = {"D4", "D5-O", "D5-M"}


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


def _expected_demotion(row):
    return f"{row['terminal_verdict']}/{row['discovery_level']}"


def test_witness_ledger_has_exact_kinds_and_soundness_fields():
    payload = _checked_in_payload()
    witnesses = payload["witnesses"]

    assert payload["artifact_id"] == "bedc-quality-lab:discovery-negative-witnesses"
    assert payload["status"] == "pointer-only"
    assert payload["expected_kind_count"] == 9
    assert [row["kind"] for row in witnesses] == list(generator.EXPECTED_KINDS)
    for row in witnesses:
        assert isinstance(row["soundness"], str)
        assert row["soundness"].strip()


def test_each_witness_has_bedc_gap_contract():
    payload = _checked_in_payload()
    witnesses = payload["witnesses"]

    assert set(EXPECTED_GAP_FIELDS) == set(generator.EXPECTED_KINDS)
    assert not hasattr(canonical, "NEGATIVE_WITNESSES_REQUIRED_FIELDS")
    assert {row["kind"]: row["bedc_gap_field"] for row in witnesses} == EXPECTED_GAP_FIELDS
    for row in witnesses:
        contract = generator.WITNESS_GAP_CONTRACTS[row["kind"]]
        for field in generator.REQUIRED_GAP_FIELDS:
            assert isinstance(row[field], str)
            assert row[field].strip()
            assert row[field] == getattr(contract, field)


def test_witness_ledger_stays_outside_report_and_scorecard_schema_boundary():
    payload = _checked_in_payload()
    keys = set(_walk_keys(payload))
    text = json.dumps(payload, sort_keys=True)

    assert keys.isdisjoint(FORBIDDEN_LEDGER_FIELDS)
    assert "host.env" not in text
    assert "QualityEvidenceEnvelope" not in text
    assert "quality_scorecard" not in keys
    assert "scorecard" not in keys
    assert "jet_negative_witnesses.json" not in text
    assert "derivative_debt_ledger.json" not in text


@pytest.mark.parametrize("kind", generator.EXPECTED_KINDS)
def test_each_pseudo_witness_fails_closed_under_current_verdict_gate(decisions_by_kind, kind):
    decision = _decision_for_kind(decisions_by_kind, kind)
    projected = assign_discovery_level(decision)

    assert decision["verdict"] in {"rejected", "demoted", "ledger-only"}
    assert decision["verdict"] != "positive-discovery"
    assert projected.discovery_level not in POSITIVE_DISCOVERY_LEVELS


def test_gap_witness_demotions_match_gate_replay(decisions_by_kind):
    payload = _checked_in_payload()
    rows_by_kind = {row["kind"]: row for row in payload["witnesses"]}

    for kind in generator.EXPECTED_KINDS:
        row = rows_by_kind[kind]
        decision = _decision_for_kind(decisions_by_kind, kind)
        projected = assign_discovery_level(decision)
        assert row["terminal_verdict"] == decision["verdict"]
        assert row["discovery_level"] == projected.discovery_level
        assert row["demotion_rule"] == _expected_demotion(row)
        assert row["demotion_rule"] == generator.WITNESS_GAP_CONTRACTS[kind].demotion_rule
        assert projected.discovery_level not in POSITIVE_DISCOVERY_LEVELS


def test_cost_protocol_missing_and_scorecard_not_ready_never_reach_positive_levels(decisions_by_kind):
    cost = _decision_for_kind(decisions_by_kind, "cost_protocol_missing")
    scorecard = _decision_for_kind(decisions_by_kind, "scorecard_not_ready")

    assert cost["verdict"] in {"rejected", "ledger-only"}
    assert assign_discovery_level(cost).discovery_level not in POSITIVE_DISCOVERY_LEVELS
    assert scorecard["verdict"] in {"rejected", "ledger-only"}
    assert assign_discovery_level(scorecard).discovery_level not in POSITIVE_DISCOVERY_LEVELS


def test_gap_witness_regression_pointers_resolve_to_behavior_tests():
    payload = _checked_in_payload()
    nodeids = [row["regression_test_pointer"] for row in payload["witnesses"]]

    assert len(nodeids) == len(set(nodeids))
    for nodeid in nodeids:
        assert nodeid.startswith("tests/test_")
        assert "::test_" in nodeid
        lowered = nodeid.lower()
        assert not any(term in lowered for term in FORBIDDEN_REGRESSION_POINTER_TERMS)
        if nodeid != (
            "tests/test_discovery_negative_witnesses.py::"
            "test_synthetic_leakage_injection_witness_fails_closed"
        ):
            assert not nodeid.startswith("tests/test_discovery_negative_witnesses.py::")

    result = subprocess.run(
        [sys.executable, "-m", "pytest", "--collect-only", "-q", *nodeids],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    for nodeid in nodeids:
        assert nodeid in result.stdout


@pytest.mark.parametrize("field", generator.REQUIRED_GAP_FIELDS)
def test_gap_witness_validator_rejects_prose_only_rows(field):
    payload = _checked_in_payload()
    payload["witnesses"][0] = dict(payload["witnesses"][0])
    del payload["witnesses"][0][field]

    with pytest.raises(RuntimeError, match=field):
        generator.validate_witness_gap_contracts(payload)


def test_replay_matches_checked_in_gap_witness_ledger():
    replayed = generator.replay_checked_in_ledger(LEDGER_PATH)

    assert replayed == _checked_in_payload()


def test_write_witness_ledger_refresh_preserves_existing_generated_at(tmp_path, monkeypatch):
    monkeypatch.setattr(generator, "ROOT", tmp_path)
    target = tmp_path / generator.LEDGER_ARTIFACT
    sentinel = "2040-01-02T03:04:05+00:00"
    existing = generator.build_witness_ledger(generated_at=sentinel)
    target.parent.mkdir(parents=True)
    target.write_text(json.dumps(existing, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    payload = generator.write_witness_ledger(target)
    written = json.loads(target.read_text(encoding="utf-8"))

    assert payload["generated_at"] == sentinel
    assert written["generated_at"] == sentinel
    assert written == payload


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
        "expected_kind_count": 9,
        "schema_role": "bedc-gap-witness-ledger",
        "witness_rows_pointer": "reports/canonical/discovery_negative_witnesses.json:$.witnesses",
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


def test_synthetic_leakage_injection_witness_fails_closed(runtime_by_kind, decisions_by_kind):
    witness = runtime_by_kind["synthetic_leakage_injection"]
    decision = decisions_by_kind["synthetic_leakage_injection"]
    projected = assign_discovery_level(decision)

    injection = witness.evidence_payload["synthetic_leakage_injection"]
    assert injection["label"] == "synthetic-positive-label"
    assert "error" in injection or "prediction_error" in injection
    assert injection["prediction_error"] == 0.0
    assert injection["metadata"]["config_derived_cell"] == "config_metadata.seed"
    assert set(injection["injected_surfaces"]) == {
        "label",
        "prediction_error",
        "error",
        "config_metadata.seed",
    }
    assert witness.certificate_payload["synthetic_leakage_injection"] == injection
    assert decision["verdict"] in {"rejected", "demoted", "ledger-only"}
    assert decision["verdict"] != "positive-discovery"
    assert projected.discovery_level not in POSITIVE_DISCOVERY_LEVELS
