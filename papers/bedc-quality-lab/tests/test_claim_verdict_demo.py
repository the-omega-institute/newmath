import json
from pathlib import Path

import pytest

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from scripts import run_claim_verdict_demo as demo
from scripts import run_canonical_reports as canonical


ALLOWED_KEYS = {"claim_id", "claim_verdict", "reason", "source", "ledger_pointer"}
VERDICT_NAMES = {
    "accepted_positive_discovery",
    "audit_improvement_only",
    "certified_discovery_not_positive",
    "discovery_candidate",
    "negative_discovery",
    "revoked_due_to_fresh_evidence",
    "rejected_due_to_hidden_debt",
    "rejected_due_to_scope_laundering",
}
DOWNGRADE_VERDICTS = {
    "negative_discovery",
    "revoked_due_to_fresh_evidence",
    "rejected_due_to_hidden_debt",
    "rejected_due_to_scope_laundering",
}


def _scorecard(status="ready"):
    return {
        "rows": [
            {"metric": metric, "status": status, "value": index}
            for index, metric in enumerate(canonical.QUALITY_SCORECARD_METRICS)
        ]
    }


def _write_json(path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _base_payload():
    return {
        "source_artifacts": {"cost_protocol": "configs/default_cost_protocol.yaml"},
        "applicability_boundary": {"not_claimed": "fixture"},
        "positive_discovery": False,
        "matched_random_control": {"control_verdict": {"positive": False}},
        "claim_gate": {"training_audit_improvement_tradeoff": False},
        "main_verdict": {"surface_delta_count": 0, "shift_information": 0, "deltas": {"debt_delta": 0}},
        "net_information": 0.0,
    }


def _payload_for_level(level):
    payload = _base_payload()
    if level in {"D4", "D5"}:
        payload.update(
            {
                "positive_discovery": True,
                "net_information": 1.0,
                "net_positive_signal": True,
                "matched_random_control": {"control_verdict": {"positive": False}},
            }
        )
        if level == "D5":
            payload["acceptance_gates"] = {"status": "pass"}
            payload["final_status"] = "pass"
    elif level == "D3":
        payload["main_verdict"] = {"structural_discovery": True, "surface_delta_count": 1, "shift_information": 1}
    elif level == "D2":
        payload["main_verdict"] = {"surface_delta_count": 1, "shift_information": 1}
    elif level == "D1":
        payload["main_verdict"] = {"deltas": {"debt_delta": -1}}
    elif level == "DN":
        payload["verdict"] = "rejected"
    elif level == "DR":
        payload["revocation_decision"] = {"downgraded": True, "new_status": "revoked"}
    return payload


def _spec(name, artifact, *, scope="$.scope", cost="$.cost", not_claimed="$.not_claimed", positive="$.positive"):
    return canonical.CanonicalReportSpec(
        name=name,
        command=("python3", "scripts/run_fixture.py"),
        json_artifact=artifact,
        markdown_artifact=artifact.replace(".json", ".md"),
        required_json_keys=("source_artifacts",),
        estimated_seconds=1,
        bundle_role="hg_p_core",
        scope_pointer=scope,
        cost_pointer=cost,
        not_claimed_pointer=not_claimed,
        positive_claim_pointer=positive,
        control_pointer="$.control",
        no_control_rationale_pointer=None,
    )


def _fixture_root(tmp_path, monkeypatch, rows, payloads, witnesses=()):
    monkeypatch.setattr(demo, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(demo, "CANONICAL_REPORTS", tuple(payloads))
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", tuple(payloads))
    _write_json(tmp_path / "reports/canonical/discovery_map.json", {"rows": rows})
    _write_json(tmp_path / "reports/canonical/quality-scorecard.json", _scorecard())
    _write_json(tmp_path / "reports/canonical/discovery_negative_witnesses.json", {"witnesses": list(witnesses)})
    (tmp_path / "configs").mkdir(parents=True, exist_ok=True)
    (tmp_path / "configs/default_cost_protocol.yaml").write_text(
        (Path(__file__).resolve().parents[1] / "configs/default_cost_protocol.yaml").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    for spec in payloads:
        payload = _payload_for_level(rows_by_report(rows)[spec.name])
        payload.update(
            {
                "scope": {"status": "present"},
                "cost": {"status": "present"},
                "not_claimed": ["fixture"],
                "positive": {"claim": "fixture"},
                "control": {"status": "present"},
            }
        )
        _write_json(tmp_path / spec.json_artifact, payload)
    return tmp_path


def rows_by_report(rows):
    return {row["report"]: row["discovery_level"] for row in rows}


def _discovery_row(report, artifact, level, pointer="$.positive_discovery"):
    row = {
        "report": report,
        "json_artifact": artifact,
        "markdown_artifact": artifact.replace(".json", ".md"),
        "discovery_level": level,
        "terminal_verdict": "",
        "classifier_reasons": [f"fixture-{level}"],
        "projection_status": "projected",
        "evidence_pointer": pointer,
        "audit_status": "valid",
        "audit_reason": "",
    }
    if level == "DN":
        row["failed_gate"] = "$.verdict"
    if level == "DR":
        row["failed_gate"] = "$.revocation_decision"
    if level == "D1":
        row["debt_row_pointer"] = "$.main_verdict.deltas.debt_delta"
    return row


def test_all_eight_claim_verdict_names_are_reachable(tmp_path, monkeypatch):
    rows = [
        _discovery_row("d4", "reports/canonical/d4.json", "D4"),
        _discovery_row("d1", "reports/canonical/d1.json", "D1"),
        _discovery_row("d3", "reports/canonical/d3.json", "D3"),
        _discovery_row("d2", "reports/canonical/d2.json", "D2"),
        _discovery_row("dn", "reports/canonical/dn.json", "DN"),
        _discovery_row("d0", "reports/canonical/d0.json", "D0"),
    ]
    specs = tuple(_spec(row["report"], row["json_artifact"]) for row in rows)
    witnesses = [
        {"kind": "hidden_debt_positive", "terminal_verdict": "demoted", "terminal_reason": "audit-improvement-tradeoff", "discovery_level": "DR", "gate_basis": {"new_status": "audit-improvement-tradeoff"}},
        {"kind": "fresh_claim_downgrade", "terminal_verdict": "demoted", "terminal_reason": "audit-improvement-tradeoff", "discovery_level": "DR", "gate_basis": {"new_status": "audit-improvement-tradeoff"}},
        {"kind": "forbidden_inference_column", "terminal_verdict": "rejected", "terminal_reason": "overclaim", "discovery_level": "DN", "gate_basis": {"forbidden_claim_term_hits": [FORBIDDEN_POSITIVE_CLAIM_TERMS[0]]}},
    ]
    _fixture_root(tmp_path, monkeypatch, rows, specs, witnesses)

    verdicts = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert {row["claim_verdict"] for row in verdicts} == VERDICT_NAMES
    assert "claim:d0" not in {row["claim_id"] for row in verdicts}


def test_jsonl_row_schema_reason_and_downgrade_pointers(tmp_path, monkeypatch):
    rows = [_discovery_row("dn", "reports/canonical/dn.json", "DN")]
    specs = (_spec("dn", "reports/canonical/dn.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdicts = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    for row in verdicts:
        assert set(row) == ALLOWED_KEYS
        assert row["reason"]
        assert "schema_id" not in row
        assert "SCHEMA_ID" not in row
        if row["claim_verdict"] in DOWNGRADE_VERDICTS:
            assert row["ledger_pointer"]


def test_forbidden_overclaim_preempts_positive_acceptance_and_uses_claim_terms(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["positive"] = {"claim": f"{FORBIDDEN_POSITIVE_CLAIM_TERMS[0]} certificate"}
    _write_json(payload_path, payload)

    verdicts = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert verdicts[0]["claim_verdict"] == "rejected_due_to_scope_laundering"
    assert verdicts[0]["reason"] == "forbidden-overclaim"
    assert verdicts[0]["ledger_pointer"] == "reports/canonical/d4.json:$.positive"


def test_missing_cost_protocol_and_not_ready_scorecard_fail_closed(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    (tmp_path / "configs/default_cost_protocol.yaml").unlink()

    cost_verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]
    assert cost_verdict["claim_verdict"] == "rejected_due_to_hidden_debt"
    assert cost_verdict["reason"] == "cost-protocol-unavailable"

    (tmp_path / "configs/default_cost_protocol.yaml").write_text(
        (Path(__file__).resolve().parents[1] / "configs/default_cost_protocol.yaml").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    _write_json(tmp_path / "reports/canonical/quality-scorecard.json", _scorecard(status="not-ready"))
    scorecard_verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]
    assert scorecard_verdict["claim_verdict"] == "rejected_due_to_hidden_debt"
    assert scorecard_verdict["reason"] == "scorecard-not-ready"


def test_demoted_terminal_positive_discovery_fails_closed_with_ledger_pointer(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    def synthesize_demoted(certificate_payload, evidence_payload, *, timestamp_iso):
        assert certificate_payload is None
        assert timestamp_iso == "2030-01-01T00:00:00+00:00"
        assert evidence_payload["quality_scorecard"] == _scorecard()
        return {"verdict": "demoted", "reason": "audit-improvement-tradeoff"}

    monkeypatch.setattr(demo, "synthesize_certification_verdict", synthesize_demoted)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "rejected_due_to_hidden_debt"
    assert verdict["reason"] == "audit-improvement-tradeoff"
    assert verdict["ledger_pointer"] == "reports/canonical/d4.json:$.cost"


def test_scope_laundering_cell_rejects_with_real_pointer(tmp_path, monkeypatch):
    rows = [_discovery_row("gap-head-discovery", "reports/canonical/gap-head-discovery.json", "D4")]
    specs = (_spec("gap-head-discovery", "reports/canonical/gap-head-discovery.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/gap-head-discovery.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["laundering_modes"] = ["metric_only"]
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "rejected_due_to_scope_laundering"
    assert verdict["reason"] == "scope-discipline-failed"
    assert verdict["ledger_pointer"] == "reports/canonical/gap-head-discovery.json:$.laundering_modes"


def test_cli_writes_jsonl(tmp_path, monkeypatch):
    rows = [_discovery_row("d1", "reports/canonical/d1.json", "D1")]
    specs = (_spec("d1", "reports/canonical/d1.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    written = demo.write_claim_verdicts(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    lines = (tmp_path / demo.CLAIM_VERDICTS_JSONL_ARTIFACT).read_text(encoding="utf-8").splitlines()

    assert [json.loads(line) for line in lines] == written
