import json
from pathlib import Path

import pytest

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from scripts import run_claim_verdict_demo as demo
from scripts import run_canonical_reports as canonical


ALLOWED_KEYS = {
    "claim_id",
    "claim_verdict",
    "reason",
    "source",
    "ledger_pointer",
}
DIMENSION_MISMATCH_ALLOWED_KEYS = {
    "claim_id",
    "claim_verdict",
    "reason",
    "source",
    "ledger_pointer",
    "hypothesis",
    "failed_gate",
    "what_was_learned",
    "downgrade_reason",
}
VERDICT_NAMES = {
    "accepted_positive_discovery",
    "demoted_audit_tradeoff",
    "ledger_only_hardening_not_ready",
    "rejected_hidden_debt",
    "rejected_scope_laundering",
}
DOWNGRADE_VERDICTS = {
    "demoted_audit_tradeoff",
    "ledger_only_hardening_not_ready",
    "rejected_hidden_debt",
    "rejected_scope_laundering",
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


def _spec(
    name,
    artifact,
    *,
    scope="$.scope",
    cost="$.cost",
    not_claimed="$.not_claimed",
    positive="$.positive",
    control="$.control",
):
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
        control_pointer=control,
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


def _dimension_mismatch_discovery_row(level="D4"):
    row = _discovery_row(
        "dimension-mismatch-debt-transfer",
        "reports/canonical/dimension-mismatch-debt-transfer.json",
        level,
        pointer="$.dimension_mismatch_debt_transfer.effective_level",
    )
    row["control_pointer"] = "$.control_protocol"
    if level == "DN":
        row["failed_gate"] = "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    return row


def _dimension_mismatch_payload(*, status="pass", forbidden_claim=None):
    claim = {
        "status": status,
        "status_code": "scoped-d4-boundary" if status == "pass" else "failed-boundary",
        "reason": "fixture",
        "scope": "encoder_dim grid against producer reference latent dimension",
        "discovery_level": "D4" if status == "pass" else "DN",
        "pass_surface_count": 1 if status == "pass" else 0,
        "total_surface_count": 1,
        "discovery_map_pointer": "$.dimension_mismatch_debt_transfer.effective_level",
    }
    if forbidden_claim is not None:
        claim["claim"] = forbidden_claim
    return {
        "artifact_id": "bedc-quality-lab:dimension-mismatch-debt-transfer",
        "artifact": "reports/canonical/dimension-mismatch-debt-transfer.json",
        "status": "pointer-only",
        "source_artifacts": {"cost_protocol": "configs/default_cost_protocol.yaml"},
        "control_protocol": {"control_arm": "matched_random", "same_feature_columns_as_treatment": True},
        "dimension_mismatch_debt_transfer": claim,
        "not_claimed": ["fixture"],
    }


def _dimension_mismatch_downgraded_payload():
    payload = _dimension_mismatch_payload(status="pass")
    payload["dimension_mismatch_debt_transfer"].update(
        {
            "base_level": "D4",
            "anti_triviality_status": "scale_leakage_detected",
            "effective_level": "DN",
            "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
            "terminal_verdict": "negative_discovery",
            "discovery_level": "DN",
            "hypothesis": "fixture hypothesis",
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "what_was_learned": "fixture learned",
        }
    )
    return payload


def test_claim_verdict_names_are_reachable(tmp_path, monkeypatch):
    rows = [
        _discovery_row("d4", "reports/canonical/d4.json", "D4"),
        _discovery_row("d1", "reports/canonical/d1.json", "D1"),
        _discovery_row("d3", "reports/canonical/d3.json", "D3"),
        _discovery_row("d2", "reports/canonical/d2.json", "D2"),
        _discovery_row("dn", "reports/canonical/dn.json", "DN"),
        _discovery_row("d0", "reports/canonical/d0.json", "D0"),
    ]
    rows[-2]["failed_gate"] = "$.cost.hidden_debt"
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

    assert verdicts[0]["claim_verdict"] == "rejected_scope_laundering"
    assert verdicts[0]["reason"] == "forbidden-overclaim"
    assert verdicts[0]["ledger_pointer"] == "reports/canonical/d4.json:$.positive"


def test_missing_cost_protocol_and_not_ready_scorecard_fail_closed(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    (tmp_path / "configs/default_cost_protocol.yaml").unlink()

    cost_verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]
    assert cost_verdict["claim_verdict"] == "rejected_hidden_debt"
    assert cost_verdict["reason"] == "cost-protocol-unavailable"

    (tmp_path / "configs/default_cost_protocol.yaml").write_text(
        (Path(__file__).resolve().parents[1] / "configs/default_cost_protocol.yaml").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    _write_json(tmp_path / "reports/canonical/quality-scorecard.json", _scorecard(status="not-ready"))
    scorecard_verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]
    assert scorecard_verdict["claim_verdict"] == "ledger_only_hardening_not_ready"
    assert scorecard_verdict["reason"] == "scorecard-not-ready"
    assert scorecard_verdict["ledger_pointer"].startswith("reports/canonical/quality-scorecard.json:$.rows")


def test_hardening_coverage_not_ready_uses_dependency_pointer(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    scorecard = _scorecard()
    hardening_index = next(
        index for index, row in enumerate(scorecard["rows"]) if row["metric"] == "HardeningCoverage"
    )
    scorecard["rows"][hardening_index]["status"] = "not-ready"
    _write_json(tmp_path / "reports/canonical/quality-scorecard.json", scorecard)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "ledger_only_hardening_not_ready"
    assert verdict["reason"] == "scorecard-not-ready"
    assert verdict["ledger_pointer"] == f"reports/canonical/quality-scorecard.json:$.rows[{hardening_index}]"


def test_positive_discovery_gate_failure_routes_to_ledger_only_hardening_not_ready(tmp_path, monkeypatch):
    rows = [_discovery_row("gap-head-on-h", "reports/canonical/gap-head-on-h.json", "D5")]
    rows[0]["control_pointer"] = "$.matched_random_control.control_verdict.positive"
    specs = (
        _spec(
            "gap-head-on-h",
            "reports/canonical/gap-head-on-h.json",
            control="$.matched_random_control.control_verdict.positive",
        ),
    )
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/gap-head-on-h.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["matched_random_control"]["control_verdict"]["positive"] = True
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:gap-head-on-h"
    assert verdict["claim_verdict"] == "ledger_only_hardening_not_ready"
    assert verdict["reason"] == "positive-discovery-gate-failed"
    assert verdict["source"] == "reports/canonical/gap-head-on-h.json:$.positive_discovery"
    assert verdict["ledger_pointer"] == (
        "reports/canonical/gap-head-on-h.json:"
        "$.matched_random_control.control_verdict.positive"
    )


@pytest.mark.parametrize("audit_status", ["invalid", None])
def test_positive_discovery_requires_valid_discovery_map_audit(tmp_path, monkeypatch, audit_status):
    rows = [_discovery_row("gap-head-discovery", "reports/canonical/gap-head-discovery.json", "D4")]
    if audit_status is None:
        rows[0].pop("audit_status")
    else:
        rows[0]["audit_status"] = audit_status
    specs = (_spec("gap-head-discovery", "reports/canonical/gap-head-discovery.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:gap-head-discovery"
    assert verdict["claim_verdict"] == "ledger_only_hardening_not_ready"
    assert verdict["reason"] == "discovery-map-audit-not-valid"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].audit_status"


def test_positive_discovery_accepts_valid_discovery_map_audit(tmp_path, monkeypatch):
    rows = [_discovery_row("gap-head-discovery", "reports/canonical/gap-head-discovery.json", "D4")]
    specs = (_spec("gap-head-discovery", "reports/canonical/gap-head-discovery.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:gap-head-discovery"
    assert verdict["claim_verdict"] == "accepted_positive_discovery"
    assert verdict["reason"] == "positive-discovery-gates-pass"


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

    assert verdict["claim_verdict"] == "demoted_audit_tradeoff"
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

    assert verdict["claim_verdict"] == "rejected_scope_laundering"
    assert verdict["reason"] == "scope-discipline-failed"
    assert verdict["ledger_pointer"] == "reports/canonical/gap-head-discovery.json:$.laundering_modes"


def test_noncanonical_dimension_mismatch_discovery_row_emits_negative_claim_verdict(tmp_path, monkeypatch):
    rows = [_dimension_mismatch_discovery_row("DN")]
    _fixture_root(tmp_path, monkeypatch, rows, ())
    _write_json(
        tmp_path / "reports/canonical/dimension-mismatch-debt-transfer.json",
        _dimension_mismatch_downgraded_payload(),
    )

    verdicts = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    by_claim = {row["claim_id"]: row for row in verdicts}
    verdict = by_claim["claim:dimension-mismatch-debt-transfer"]

    assert "dimension-mismatch-debt-transfer.json" not in {
        Path(spec.json_artifact).name for spec in canonical.CANONICAL_REPORTS
    }
    assert set(verdict) == DIMENSION_MISMATCH_ALLOWED_KEYS
    assert verdict["claim_verdict"] == "negative_discovery"
    assert verdict["reason"] == "discovery-level-DN"
    assert verdict["source"] == (
        "reports/canonical/dimension-mismatch-debt-transfer.json:"
        "$.dimension_mismatch_debt_transfer.effective_level"
    )
    assert verdict["ledger_pointer"] == (
        "reports/canonical/dimension-mismatch-debt-transfer.json:"
        "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    )
    assert verdict["hypothesis"] == "fixture hypothesis"
    assert verdict["failed_gate"] == "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    assert verdict["what_was_learned"] == "fixture learned"
    assert verdict["downgrade_reason"] == "scale_only_or_metadata_proxy_sufficient"
    discovery_map = json.loads((tmp_path / "reports/canonical/discovery_map.json").read_text(encoding="utf-8"))
    assert discovery_map["rows"][0]["discovery_level"] == "DN"


def test_noncanonical_dimension_mismatch_dn_ignores_positive_scorecard_gate(tmp_path, monkeypatch):
    rows = [_dimension_mismatch_discovery_row("DN")]
    _fixture_root(tmp_path, monkeypatch, rows, ())
    _write_json(
        tmp_path / "reports/canonical/dimension-mismatch-debt-transfer.json",
        _dimension_mismatch_downgraded_payload(),
    )
    _write_json(tmp_path / "reports/canonical/quality-scorecard.json", _scorecard(status="not-ready"))

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:dimension-mismatch-debt-transfer"
    assert verdict["claim_verdict"] == "negative_discovery"
    assert verdict["reason"] == "discovery-level-DN"
    assert verdict["downgrade_reason"] == "scale_only_or_metadata_proxy_sufficient"


def test_noncanonical_dimension_mismatch_dn_requires_valid_discovery_map_audit(tmp_path, monkeypatch):
    rows = [_dimension_mismatch_discovery_row("DN")]
    rows[0]["audit_status"] = "invalid"
    _fixture_root(tmp_path, monkeypatch, rows, ())
    _write_json(
        tmp_path / "reports/canonical/dimension-mismatch-debt-transfer.json",
        _dimension_mismatch_downgraded_payload(),
    )

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:dimension-mismatch-debt-transfer"
    assert verdict["claim_verdict"] == "ledger_only_hardening_not_ready"
    assert verdict["reason"] == "discovery-map-audit-not-valid"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].audit_status"


def test_noncanonical_dimension_mismatch_missing_cells_do_not_emit_negative_claim_verdict(tmp_path, monkeypatch):
    rows = [_dimension_mismatch_discovery_row("DN")]
    _fixture_root(tmp_path, monkeypatch, rows, ())
    payload = _dimension_mismatch_downgraded_payload()
    payload["dimension_mismatch_debt_transfer"].pop("what_was_learned")
    _write_json(
        tmp_path / "reports/canonical/dimension-mismatch-debt-transfer.json",
        payload,
    )

    with pytest.raises(ValueError, match="source cells missing"):
        demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")


def test_noncanonical_dimension_mismatch_forbidden_claim_rejects_with_pointer(tmp_path, monkeypatch):
    rows = [_dimension_mismatch_discovery_row()]
    _fixture_root(tmp_path, monkeypatch, rows, ())
    term = FORBIDDEN_POSITIVE_CLAIM_TERMS[0]
    _write_json(
        tmp_path / "reports/canonical/dimension-mismatch-debt-transfer.json",
        _dimension_mismatch_payload(forbidden_claim=term),
    )

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:dimension-mismatch-debt-transfer"
    assert verdict["claim_verdict"] == "rejected_scope_laundering"
    assert verdict["reason"] == "forbidden-overclaim"
    assert verdict["ledger_pointer"] == (
        "reports/canonical/dimension-mismatch-debt-transfer.json:"
        "$.dimension_mismatch_debt_transfer"
    )


def test_cli_writes_jsonl(tmp_path, monkeypatch):
    rows = [_discovery_row("d1", "reports/canonical/d1.json", "D1")]
    specs = (_spec("d1", "reports/canonical/d1.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    written = demo.write_claim_verdicts(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    lines = (tmp_path / demo.CLAIM_VERDICTS_JSONL_ARTIFACT).read_text(encoding="utf-8").splitlines()

    assert [json.loads(line) for line in lines] == written
