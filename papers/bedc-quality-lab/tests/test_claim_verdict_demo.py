import json
from pathlib import Path

import pytest

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.evidence_provenance import build_evidence_provenance
from bedc_quality_lab.discovery_compiler.claim_verdict_reason import (
    ClaimVerdictReasonBasis,
    reason_for_claim_verdict,
    validate_claim_verdict_reason,
)
from scripts import run_claim_verdict_demo as demo
from scripts import run_canonical_reports as canonical
from bedc_quality_lab import high_impact_review


ALLOWED_KEYS = {
    "claim_id",
    "claim_graph_node_id",
    "claim_verdict",
    "reason",
    "source",
    "ledger_pointer",
    "scorecard_pointer",
    "scorecard_hash",
    "scorecard_ready",
    "formal_hardening_ready",
}
DN_ALLOWED_KEYS = {
    "claim_id",
    "claim_graph_node_id",
    "claim_verdict",
    "reason",
    "negative_report_pointer",
}
VERDICT_NAMES = {
    "raw_operational_evidence_pass",
    "projected_discovery_required",
    "projected_positive_discovery",
    "accepted_positive_discovery",
    "mechanism_not_closed",
    "negative_discovery",
    "revoked_discovery",
}
VALID_SCOPE_SEAL = {
    "status": "closed",
    "toy": True,
    "bounded": True,
    "theorem": False,
    "real_training": False,
    "production_forbidden": True,
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


def _ensure_pointer_value(payload, pointer, value):
    if pointer is None or not pointer.startswith("$."):
        return
    target = payload
    parts = pointer[2:].split(".")
    for part in parts[:-1]:
        child = target.get(part)
        if not isinstance(child, dict):
            child = {}
            target[part] = child
        target = child
    target.setdefault(parts[-1], value)


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
    if level in {"D4", "D5-O", "D5-M"}:
        payload.update(
            {
                "positive_discovery": True,
                "net_information": 1.0,
                "net_positive_signal": True,
                "main_verdict": {
                    "surface_delta_count": 1,
                    "shift_information": 1,
                    "structural_discovery": True,
                    "net_information": 1.0,
                    "deltas": {"debt_delta": 0},
                },
                "evidence_basis": {
                    "control_positive_discovery": False,
                    "scorecard_ready": True,
                    "audit_status": "valid",
                },
                "matched_random_control": {"control_verdict": {"positive": False}},
                "scope_seal": VALID_SCOPE_SEAL,
            }
        )
        if level in {"D5-O", "D5-M"}:
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
    no_control_rationale=None,
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
        no_control_rationale_pointer=no_control_rationale,
    )


def _fixture_root(tmp_path, monkeypatch, rows, payloads, witnesses=()):
    monkeypatch.setattr(demo, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(demo, "CANONICAL_REPORTS", tuple(payloads))
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", tuple(payloads))
    _write_json(tmp_path / "reports/canonical/discovery_map.json", {"rows": rows})
    _write_json(tmp_path / "reports/canonical/quality-scorecard.json", _scorecard())
    _write_json(
        tmp_path / "reports/canonical/formal_hardening.json",
        {"ready": True, "recorded": 1, "required": 1, "gap_count": 0},
    )
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
                "no_control_rationale": {"reason": "fixture"},
                "claim_capsule_ref": f"reports/runs/{spec.name}/claim_capsule.json",
            }
        )
        _ensure_pointer_value(payload, spec.scope_pointer, {"status": "present"})
        _ensure_pointer_value(payload, spec.cost_pointer, {"status": "present"})
        _ensure_pointer_value(payload, spec.not_claimed_pointer, ["fixture"])
        _ensure_pointer_value(payload, spec.positive_claim_pointer, {"claim": "fixture"})
        _ensure_pointer_value(payload, spec.control_pointer, {"status": "present"})
        _ensure_pointer_value(payload, spec.no_control_rationale_pointer, {"reason": "fixture"})
        _write_json(tmp_path / spec.json_artifact, payload)
        _write_json(
            tmp_path / f"reports/runs/{spec.name}/claim_capsule.json",
            {
                "schema_id": "bedc.quality.claim_capsule",
                "claim_status": "fixture",
                "not_claimed": ["fixture"],
                "what_was_learned": "fixture learned",
            },
        )
    source = tmp_path / "scripts" / "run_fixture.py"
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text("def train(loss, optimizer):\n    loss.backward()\n    optimizer.step()\n", encoding="utf-8")
    index_payload = {
        "schema_id": "bedc-quality-lab:canonical-report-index",
        "generated_at": "fixture",
        "evidence_provenance": build_evidence_provenance(
            root=tmp_path,
            canonical_reports=tuple(payloads),
            generated_at="fixture",
        ),
    }
    _write_json(tmp_path / "reports/canonical/index.json", index_payload)
    return tmp_path


def _scorecard_hash(root):
    return demo.load_scorecard_snapshot(root).scorecard_hash


def _assert_provenance(row, root, *, scorecard_ready=True, formal_hardening_ready=True):
    if set(row) == DN_ALLOWED_KEYS:
        assert set(row) == DN_ALLOWED_KEYS
        assert row["claim_graph_node_id"] == demo.terminal_node_id_for_claim_id(row["claim_id"])
        assert row["negative_report_pointer"]
        return
    assert set(row) == ALLOWED_KEYS
    assert row["claim_graph_node_id"] == demo.terminal_node_id_for_claim_id(row["claim_id"])
    assert row["claim_graph_node_id"].startswith("terminal:")
    assert row["scorecard_pointer"] == "reports/canonical/quality-scorecard.json:$.rows"
    assert row["scorecard_hash"] == _scorecard_hash(root)
    assert row["scorecard_ready"] is scorecard_ready
    assert row["formal_hardening_ready"] is formal_hardening_ready


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


def test_claim_verdict_reason_taxonomy_rejects_unknown_or_bare_dn_reason():
    with pytest.raises(ValueError, match="unsupported claim verdict reason taxonomy"):
        validate_claim_verdict_reason({"reason": "discovery-level-D0"})
    with pytest.raises(ValueError, match="bare negative discovery failed-gate"):
        validate_claim_verdict_reason({"reason": "negative-discovery-failed-gate"})
    with pytest.raises(ValueError, match="bare DN"):
        validate_claim_verdict_reason({"reason": "discovery-level-DN"})


def test_verdict_hg1_reason_cannot_contradict_scorecard_ready():
    positive = {"reason": "discovery-level-D4-positive"}
    validate_claim_verdict_reason(
        positive,
        basis=ClaimVerdictReasonBasis(
            claim_verdict="accepted_positive_discovery",
            discovery_level="D4",
            scorecard_ready=True,
        ),
    )
    with pytest.raises(ValueError, match="expected discovery-level-D4-positive"):
        validate_claim_verdict_reason(
            {"reason": "source-insufficient"},
            basis=ClaimVerdictReasonBasis(
                claim_verdict="accepted_positive_discovery",
                discovery_level="D4",
                scorecard_ready=True,
            ),
        )


def test_verdict_hg2_reason_matches_discovery_level():
    cases = [
        (
            ClaimVerdictReasonBasis(claim_verdict="accepted_positive_discovery", discovery_level="D4"),
            "discovery-level-D4-positive",
        ),
        (
            ClaimVerdictReasonBasis(claim_verdict="accepted_positive_discovery", discovery_level="D5-O"),
            "D5O-operational",
        ),
        (
            ClaimVerdictReasonBasis(claim_verdict="accepted_positive_discovery", discovery_level="D5-M"),
            "D5M-training-mechanism",
        ),
        (
            ClaimVerdictReasonBasis(claim_verdict="projected_discovery_required", discovery_level="D0"),
            "projected-discovery-required",
        ),
        (
            ClaimVerdictReasonBasis(claim_verdict="mechanism_not_closed", discovery_level="D5-O"),
            "mechanism-not-closed",
        ),
        (
            ClaimVerdictReasonBasis(
                claim_verdict="projected_discovery_required",
                discovery_level="D4",
                source_insufficient=True,
            ),
            "source-insufficient",
        ),
    ]
    for basis, reason in cases:
        assert reason_for_claim_verdict(basis) == reason
        validate_claim_verdict_reason({"reason": reason}, basis=basis)


def test_verdict_hg3_dn_reason_contains_failed_gate_token():
    with pytest.raises(ValueError, match="requires failed_gate"):
        reason_for_claim_verdict(ClaimVerdictReasonBasis(claim_verdict="negative_discovery", discovery_level="DN"))
    basis = ClaimVerdictReasonBasis(
        claim_verdict="negative_discovery",
        discovery_level="DN",
        failed_gate="$.claim_capsule.terminal_verdict",
    )
    assert reason_for_claim_verdict(basis) == "negative-discovery-failed-gate:claim-capsule-terminal-verdict"


def test_verdict_hg4_dgt_d0_mentions_model_comparison_not_ready():
    basis = ClaimVerdictReasonBasis(
        claim_verdict="projected_discovery_required",
        discovery_level="D0",
        report="discovery-gated-transformer",
        model_comparison_ready=False,
    )

    assert reason_for_claim_verdict(basis) == "model-comparison-not-ready"


def test_compile_claim_verdicts_routes_dgt_d0_to_model_comparison_reason(tmp_path, monkeypatch):
    rows = [
        _discovery_row(
            "discovery-gated-transformer",
            "reports/canonical/discovery-gated-transformer.json",
            "D0",
        )
    ]
    _fixture_root(tmp_path, monkeypatch, rows, ())

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    _assert_provenance(verdict, tmp_path)
    assert verdict["claim_id"] == "claim:discovery-gated-transformer"
    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "model-comparison-not-ready"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].discovery_level"


def test_claim_verdict_names_are_reachable(tmp_path, monkeypatch):
    rows = [
        _discovery_row("d4", "reports/canonical/d4.json", "D4"),
        _discovery_row("d1", "reports/canonical/d1.json", "D1"),
        _discovery_row("d3", "reports/canonical/d3.json", "D3"),
        _discovery_row("d2", "reports/canonical/d2.json", "D2"),
        _discovery_row("dn", "reports/canonical/dn.json", "DN"),
        _discovery_row("d0", "reports/canonical/d0.json", "D0"),
        _discovery_row("projected-d4", "reports/canonical/projected-d4.json", "D4"),
        _discovery_row("d5o", "reports/canonical/d5o.json", "D5-O"),
    ]
    next(row for row in rows if row["report"] == "dn")["failed_gate"] = "$.cost.hidden_debt"
    next(row for row in rows if row["report"] == "d5o")["terminal_verdict"] = "mechanism_not_closed"
    specs = tuple(_spec(row["report"], row["json_artifact"]) for row in rows)
    witnesses = [
        {"kind": "hidden_debt_positive", "terminal_verdict": "demoted", "terminal_reason": "audit-improvement-tradeoff", "discovery_level": "DR", "gate_basis": {"new_status": "audit-improvement-tradeoff"}},
        {"kind": "fresh_claim_downgrade", "terminal_verdict": "demoted", "terminal_reason": "audit-improvement-tradeoff", "discovery_level": "DR", "gate_basis": {"new_status": "audit-improvement-tradeoff"}},
        {"kind": "cost_protocol_missing", "terminal_verdict": "rejected", "terminal_reason": "cost-protocol-missing", "discovery_level": "DN", "gate_basis": {}},
        {"kind": "forbidden_inference_column", "terminal_verdict": "rejected", "terminal_reason": "overclaim", "discovery_level": "DN", "gate_basis": {"forbidden_claim_term_hits": [FORBIDDEN_POSITIVE_CLAIM_TERMS[0]]}},
    ]
    _fixture_root(tmp_path, monkeypatch, rows, specs, witnesses)
    projected_path = tmp_path / "reports/canonical/projected-d4.json"
    projected_payload = json.loads(projected_path.read_text(encoding="utf-8"))
    projected_payload["matched_random_control"]["control_verdict"]["positive"] = True
    _write_json(projected_path, projected_payload)

    verdicts = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert {row["claim_verdict"] for row in verdicts} == VERDICT_NAMES
    by_claim = {row["claim_id"]: row for row in verdicts}
    assert by_claim["claim:d0"]["claim_verdict"] == "projected_discovery_required"
    assert by_claim["claim:d0"]["reason"] == "projected-discovery-required"
    assert by_claim["claim:d0"]["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[5].discovery_level"
    assert all(row["claim_graph_node_id"].startswith("terminal:") for row in verdicts)


def test_claim_verdict_rows_allow_only_identity_graph_foreign_key(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert set(verdict) == ALLOWED_KEYS
    assert verdict["claim_graph_node_id"] == "terminal:d4"
    assert {
        "depends_on",
        "node_type",
        "source_pointer",
        "discovery_level",
        "terminal_verdict",
        "not_claimed",
        "hardgate",
        "mechanism_certificate",
    }.isdisjoint(verdict)


def test_jsonl_row_schema_reason_and_downgrade_pointers(tmp_path, monkeypatch):
    rows = [_discovery_row("dn", "reports/canonical/dn.json", "DN")]
    specs = (_spec("dn", "reports/canonical/dn.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdicts = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    for row in verdicts:
        _assert_provenance(row, tmp_path)
        assert row["reason"]
        assert "schema_id" not in row
        assert "SCHEMA_ID" not in row
        if set(row) == ALLOWED_KEYS:
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

    assert verdicts[0]["claim_verdict"] == "negative_discovery"
    assert verdicts[0]["reason"] == "forbidden-overclaim"
    assert verdicts[0]["ledger_pointer"] == "reports/canonical/d4.json:$.positive"


def test_missing_cost_protocol_and_not_ready_scorecard_fail_closed(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    (tmp_path / "configs/default_cost_protocol.yaml").unlink()

    cost_verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]
    assert cost_verdict["claim_verdict"] == "negative_discovery"
    assert cost_verdict["reason"] == "cost-protocol-unavailable"

    (tmp_path / "configs/default_cost_protocol.yaml").write_text(
        (Path(__file__).resolve().parents[1] / "configs/default_cost_protocol.yaml").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    _write_json(tmp_path / "reports/canonical/quality-scorecard.json", _scorecard(status="not-ready"))
    scorecard_verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]
    _assert_provenance(scorecard_verdict, tmp_path, scorecard_ready=False)
    assert scorecard_verdict["claim_verdict"] == "projected_discovery_required"
    assert scorecard_verdict["reason"] == "source-insufficient"
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

    _assert_provenance(verdict, tmp_path, scorecard_ready=False)
    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "source-insufficient"
    assert verdict["ledger_pointer"] == "reports/canonical/quality-scorecard.json:$.rows"


def test_positive_discovery_gate_failure_routes_raw_operational_case_to_raw_pass(tmp_path, monkeypatch):
    rows = [_discovery_row("gap-head-on-h", "reports/canonical/gap-head-on-h.json", "D5-O")]
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
    assert verdict["claim_verdict"] == "raw_operational_evidence_pass"
    assert verdict["reason"] == "fresh-discovery-level-DN:control_negative=false"
    assert verdict["source"] == "reports/canonical/gap-head-on-h.json:$.positive_discovery"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].discovery_level"


def test_positive_discovery_gate_failure_routes_projected_positive_case_to_projected_positive(tmp_path, monkeypatch):
    rows = [_discovery_row("projected-d4", "reports/canonical/projected-d4.json", "D4")]
    rows[0]["control_pointer"] = "$.matched_random_control.control_verdict.positive"
    specs = (
        _spec(
            "projected-d4",
            "reports/canonical/projected-d4.json",
            control="$.matched_random_control.control_verdict.positive",
        ),
    )
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/projected-d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["matched_random_control"]["control_verdict"]["positive"] = True
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:projected-d4"
    assert verdict["claim_verdict"] == "projected_positive_discovery"
    assert verdict["reason"] == "fresh-discovery-level-DN:control_negative=false"


def test_constraint_lagrangian_dn_reason_preserves_evidence_label(tmp_path, monkeypatch):
    rows = [_discovery_row("certificate-guided-training", "reports/canonical/certificate-guided-training.json", "DN")]
    rows[0]["evidence_pointer"] = "$.arm_protocol.compat_roles.after"
    rows[0]["failed_gate"] = "$.claim_capsule.terminal_verdict"
    specs = (_spec("certificate-guided-training", "reports/canonical/certificate-guided-training.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/certificate-guided-training.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload.update(
        {
            "arm_protocol": {"compat_roles": {"after": "constraint_lagrangian"}},
            "claim_capsule": {"terminal_verdict": "DN(audit-improvement-tradeoff)"},
        }
    )
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    _assert_provenance(verdict, tmp_path)
    assert verdict["claim_id"] == "claim:certificate-guided-training"
    assert verdict["reason"] == "negative-discovery-failed-gate:claim-capsule-terminal-verdict"
    assert verdict["negative_report_pointer"] == (
        "reports/canonical/certificate-guided-training.json:$.claim_capsule.terminal_verdict"
    )


def test_certificate_gated_attention_row_maps_existing_positive_verdict(tmp_path, monkeypatch):
    rows = [_discovery_row("certificate-gated-attention", "reports/canonical/certificate-gated-attention.json", "D4")]
    rows[0]["control_pointer"] = "$.matched_random_control"
    specs = (
        _spec(
            "certificate-gated-attention",
            "reports/canonical/certificate-gated-attention.json",
            positive="$.positive_claim",
            control="$.matched_random_control",
        ),
    )
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/certificate-gated-attention.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload.update(
        {
                "positive_claim": {"text": "certificate-gated attention fixture", "scope": "bounded", "scope_seal": VALID_SCOPE_SEAL},
            "matched_random_control": {"control_verdict": {"positive": False}},
            "certificate_gate_summary": {"gated_vs_plain_valid": {"leak_reduction_mean": 0.1}},
            "net_positive_signal": True,
            "positive_discovery": True,
        }
    )
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:certificate-gated-attention"
    assert verdict["claim_verdict"] in demo.CLAIM_VERDICTS
    assert verdict["claim_verdict"] == "projected_positive_discovery"


@pytest.mark.parametrize("audit_status", ["invalid", "pass", None])
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
    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "discovery-map-audit-not-valid"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].audit_status"


def test_positive_discovery_accepts_valid_discovery_map_audit(tmp_path, monkeypatch):
    rows = [_discovery_row("gap-head-discovery", "reports/canonical/gap-head-discovery.json", "D4")]
    specs = (_spec("gap-head-discovery", "reports/canonical/gap-head-discovery.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:gap-head-discovery"
    assert verdict["claim_verdict"] == "projected_positive_discovery"
    assert verdict["reason"] == "fresh-discovery-level-DN:scorecard_ready=false,audit_pass=false"


def test_stale_d4_row_capped_by_fresh_projection_does_not_emit_positive_discovery(tmp_path, monkeypatch):
    rows = [_discovery_row("stale-d4", "reports/canonical/stale-d4.json", "D4")]
    specs = (_spec("stale-d4", "reports/canonical/stale-d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/stale-d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["positive_claim"] = {"scope_seal": dict(VALID_SCOPE_SEAL, status="open")}
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:stale-d4"
    assert verdict["claim_verdict"] == "raw_operational_evidence_pass"
    assert verdict["reason"] == "fresh-discovery-level-D1:scope_seal=false"


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

    assert verdict["claim_verdict"] == "revoked_discovery"
    assert verdict["reason"] == "audit-improvement-tradeoff"
    assert verdict["ledger_pointer"] == "reports/canonical/d4.json:$.cost"


def test_formal_hardening_readiness_is_row_provenance(tmp_path, monkeypatch):
    rows = [_discovery_row("d1", "reports/canonical/d1.json", "D1")]
    specs = (_spec("d1", "reports/canonical/d1.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    _write_json(
        tmp_path / "reports/canonical/formal_hardening.json",
        {"ready": False, "recorded": 0, "required": 1, "gap_count": 1},
    )

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    _assert_provenance(verdict, tmp_path, formal_hardening_ready=False)
    assert verdict["claim_verdict"] == "raw_operational_evidence_pass"


def test_gap_head_transfer_atlas_d5_o_routes_as_positive_level(tmp_path, monkeypatch):
    rows = [
        _discovery_row(
            "gap-head-transfer-atlas",
            "reports/canonical/gap_head_transfer_atlas.json",
            "D5-O",
            pointer="$.multi_surface_d5_o.decision",
        )
    ]
    rows[0]["terminal_verdict"] = "mechanism_not_closed"
    rows[0]["control_pointer"] = "$.config.control_arm"
    specs = (
        _spec(
            "gap-head-transfer-atlas",
            "reports/canonical/gap_head_transfer_atlas.json",
            cost="$.source_artifacts.metric_helper",
            positive="$.multi_surface_d5_o",
            control="$.config.control_arm",
        ),
    )
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/gap_head_transfer_atlas.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload.update(
        {
            "config": {"control_arm": "matched_random_gap_head"},
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            },
            "multi_surface_d5_o": {"decision": "pass", "discovery_level": "D5-O"},
        }
    )
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:gap-head-transfer-atlas"
    assert verdict["claim_verdict"] == "mechanism_not_closed"
    assert verdict["reason"] != "unsupported-discovery-level"


@pytest.mark.parametrize("evidence_level", ["observational", "malformed"])
def test_d5_o_with_noncausal_mechanism_evidence_remains_mechanism_not_closed(tmp_path, monkeypatch, evidence_level):
    rows = [
        _discovery_row(
            "gap-head-attribution-capsule",
            "reports/canonical/gap_head_attribution_capsule.json",
            "D5-O",
            pointer="$.mechanism_evidence",
        )
    ]
    rows[0].update(
        {
            "mechanism_status": "ready",
            "mechanism_evidence_level": evidence_level,
            "mechanism_evidence_level_pointer": "$.mechanism_evidence.evidence_level",
            "control_pointer": "$.control_evidence",
        }
    )
    specs = (
        _spec(
            "gap-head-attribution-capsule",
            "reports/canonical/gap_head_attribution_capsule.json",
            cost="$.source_artifacts.cost_protocol",
            positive="$.mechanism_evidence",
            control="$.control_evidence",
        ),
    )
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/gap_head_attribution_capsule.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload.update(
        {
            "positive_discovery": True,
            "net_positive_signal": True,
            "control_evidence": {"status": "present"},
            "mechanism_evidence": {"evidence_level": evidence_level, "status": "ready"},
        }
    )
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:gap-head-attribution-capsule"
    assert verdict["claim_verdict"] == "mechanism_not_closed"
    assert verdict["reason"] == "mechanism-not-closed"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].discovery_level"


def test_scope_laundering_cell_rejects_with_real_pointer(tmp_path, monkeypatch):
    rows = [_discovery_row("gap-head-discovery", "reports/canonical/gap-head-discovery.json", "D4")]
    specs = (_spec("gap-head-discovery", "reports/canonical/gap-head-discovery.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/gap-head-discovery.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["laundering_modes"] = ["metric_only"]
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "negative_discovery"
    assert verdict["reason"] == "scope-discipline-failed"
    assert verdict["ledger_pointer"] == "reports/canonical/gap-head-discovery.json:$.laundering_modes"


def _add_scope_claim(payload, *, complete=True, source_scope="toy", target_scope="backend-evidence"):
    payload["scope_claim"] = {"source_scope": source_scope, "target_scope": target_scope}
    payload["scope_evidence"] = {
        "toy->bounded-design": {
            "pointer": "$.scope_gate_evidence.toy_bounded",
            "status": "resolved",
        }
    }
    payload["scope_gate_evidence"] = {"toy_bounded": {"status": "resolved"}}
    if complete:
        payload["scope_evidence"]["bounded-design->backend-evidence"] = {
            "pointer": "$.scope_gate_evidence.bounded_backend",
            "status": "resolved",
        }
        payload["scope_gate_evidence"]["bounded_backend"] = {"status": "resolved"}


def test_positive_claim_verdict_requires_scope_gate_pass(tmp_path, monkeypatch):
    rows = [_discovery_row("scope-pass", "reports/canonical/scope-pass.json", "D4")]
    specs = (_spec("scope-pass", "reports/canonical/scope-pass.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/scope-pass.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    _add_scope_claim(payload, complete=True)
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "accepted_positive_discovery"
    assert verdict["reason"] == "discovery-level-D4-positive"


def test_scope_gate_failure_produces_negative_claim_verdict(tmp_path, monkeypatch):
    rows = [_discovery_row("scope-fail", "reports/canonical/scope-fail.json", "D4")]
    rows[0]["scope_gate"] = {
        "status": "fail",
        "reason": "scope-expansion-evidence-missing",
        "failed_edge": "bounded-design->backend-evidence",
        "failed_pointer": "$.scope_evidence.bounded-design->backend-evidence",
        "required_edges": ["toy->bounded-design", "bounded-design->backend-evidence"],
    }
    specs = (_spec("scope-fail", "reports/canonical/scope-fail.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/scope-fail.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    _add_scope_claim(payload, complete=False)
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "negative_discovery"
    assert verdict["reason"] == "scope-expansion-evidence-missing"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].scope_gate"


@pytest.mark.parametrize(
    ("mutate", "reason", "ledger_pointer"),
    [
        (
            lambda payload: payload["scope_claim"].update({"source_scope": "unknown"}),
            "unknown-source-scope",
            "reports/canonical/scope-fail.json:$.scope_claim.source_scope",
        ),
        (
            lambda payload: payload["scope_claim"].update({"target_scope": "unknown"}),
            "unknown-target-scope",
            "reports/canonical/scope-fail.json:$.scope_claim.target_scope",
        ),
        (
            lambda payload: payload["scope_evidence"]["bounded-design->backend-evidence"].update(
                {"pointer": "$.scope_gate_evidence.missing"}
            ),
            "scope-expansion-evidence-missing",
            "reports/canonical/scope-fail.json:$.scope_gate_evidence.missing",
        ),
        (
            lambda payload: payload["scope_evidence"]["bounded-design->backend-evidence"].update({"pointer": ""}),
            "scope-expansion-evidence-missing",
            "reports/canonical/scope-fail.json:$.scope_evidence.bounded-design->backend-evidence.pointer",
        ),
    ],
)
def test_positive_claim_verdict_scope_payload_failures_produce_negative_discovery(
    tmp_path,
    monkeypatch,
    mutate,
    reason,
    ledger_pointer,
):
    rows = [_discovery_row("scope-fail", "reports/canonical/scope-fail.json", "D4")]
    specs = (_spec("scope-fail", "reports/canonical/scope-fail.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/scope-fail.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    _add_scope_claim(payload, complete=True)
    mutate(payload)
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "negative_discovery"
    assert verdict["reason"] == reason
    assert verdict["ledger_pointer"] == ledger_pointer


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
    _assert_provenance(verdict, tmp_path)
    assert verdict["claim_verdict"] == "negative_discovery"
    assert verdict["reason"] == (
        "negative-discovery-failed-gate:dimension-mismatch-debt-transfer-anti-triviality-status"
    )
    assert verdict["negative_report_pointer"] == (
        "reports/canonical/dimension-mismatch-debt-transfer.json:"
        "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    )
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
    assert verdict["reason"] == (
        "negative-discovery-failed-gate:dimension-mismatch-debt-transfer-anti-triviality-status"
    )
    _assert_provenance(verdict, tmp_path, scorecard_ready=False)
    assert verdict["negative_report_pointer"].endswith("$.dimension_mismatch_debt_transfer.anti_triviality_status")


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
    assert verdict["claim_verdict"] == "projected_discovery_required"
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
    assert verdict["claim_verdict"] == "negative_discovery"
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


def test_checked_in_claim_verdicts_validate_against_reason_owner():
    rows = [
        json.loads(line)
        for line in (canonical.ROOT / "reports/canonical/claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]

    assert rows
    for row in rows:
        validate_claim_verdict_reason(row)


def test_claim_verdict_rows_do_not_include_complexity_fields(tmp_path, monkeypatch):
    rows = [_discovery_row("d1", "reports/canonical/d1.json", "D1")]
    specs = (_spec("d1", "reports/canonical/d1.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert set(verdict) == ALLOWED_KEYS
    assert "claim_complexity" not in verdict
    assert "complexity_score" not in verdict
    assert "scoring_dimensions" not in verdict
    assert "pointer_only_verdict_ref" not in verdict


def test_claim_verdict_line_refs_are_stable_jsonl_pointers(tmp_path, monkeypatch):
    rows = [_discovery_row("d1", "reports/canonical/d1.json", "D1")]
    specs = (_spec("d1", "reports/canonical/d1.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    demo.write_claim_verdicts(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    refs = demo.claim_verdict_line_refs(root=tmp_path)

    assert refs == {"claim:d1": "reports/canonical/claim_verdicts.jsonl:$.lines[0]"}


@pytest.mark.parametrize(
    ("certificate", "reason"),
    [
        (None, "winnability-certificate-missing"),
        ({"status": "fail", "method": "analytic_bayes", "unwinnable": False, "coverage": {}}, "winnability-certificate-missing"),
        ({"status": "pass", "method": "analytic_bayes", "unwinnable": True, "coverage": {}}, "split-unwinnable"),
        (
            {
                "status": "pass",
                "method": "analytic_bayes",
                "unwinnable": False,
                "coverage": {"coverage_classification": "table-coverage"},
            },
            "table-coverage-ceiling",
        ),
    ],
)
def test_claim_verdict_blocks_positive_claims_with_winnability_certificates(
    tmp_path,
    monkeypatch,
    certificate,
    reason,
):
    certificate_id = "win-fixture"
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    rows[0]["winnability_ref"] = {
        "artifact": demo.WINNABILITY_CERTIFICATES_ARTIFACT,
        "certificate_id": certificate_id,
        "pointer": f"{demo.WINNABILITY_CERTIFICATES_ARTIFACT}:$.certificates[0]",
    }
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    if certificate is not None:
        _write_json(
            tmp_path / demo.WINNABILITY_CERTIFICATES_ARTIFACT,
            {
                "schema_id": "bedc-quality-lab:winnability-certificates",
                "artifact_id": "bedc-quality-lab:winnability-certificates",
                "certificates": [dict(certificate, certificate_id=certificate_id)],
                "audit": {"status": "pass"},
            },
        )

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:d4"
    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == reason
    assert verdict["ledger_pointer"] == (
        "reports/canonical/winnability-certificates.json:$.certificates[0]"
    )


def test_claim_verdict_honors_winnability_claim_permissions(tmp_path, monkeypatch):
    certificate_id = "win-deny"
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    rows[0]["winnability_ref"] = {
        "artifact": demo.WINNABILITY_CERTIFICATES_ARTIFACT,
        "certificate_id": certificate_id,
        "pointer": f"{demo.WINNABILITY_CERTIFICATES_ARTIFACT}:$.certificates[0]",
    }
    _fixture_root(tmp_path, monkeypatch, rows, (_spec("d4", "reports/canonical/d4.json"),))
    _write_json(
        tmp_path / demo.WINNABILITY_CERTIFICATES_ARTIFACT,
        {
            "schema_id": "bedc-quality-lab:winnability-certificates",
            "artifact_id": "bedc-quality-lab:winnability-certificates",
            "audit": {"status": "pass"},
            "certificates": [
                {
                    "certificate_id": certificate_id,
                    "status": "pass",
                    "method": "analytic_bayes",
                    "unwinnable": False,
                    "coverage": {"coverage_classification": "not-applicable"},
                    "claim_permissions": {
                        "memorization_claim_allowed": False,
                        "generalization_claim_allowed": False,
                        "separation_claim_allowed": False,
                        "architecture_claim_allowed": False,
                        "rule_abstraction_claim_allowed": False,
                    },
                }
            ],
        },
    )

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "winnability-permission-denied"
    assert verdict["ledger_pointer"] == "reports/canonical/winnability-certificates.json:$.certificates[0]"


@pytest.mark.parametrize(
    ("mutation", "missing_key"),
    [
        ("control", "control-or-no-control-rationale"),
        ("not_claimed", "not_claimed"),
        ("positive", "positive_claim"),
        ("scorecard_hash", "scorecard_hash"),
        ("scorecard_ready", "scorecard_ready"),
        ("claim_capsule", "claim_capsule"),
    ],
)
def test_accepted_positive_requires_acceptance_evidence_bundle(tmp_path, monkeypatch, mutation, missing_key):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    if mutation == "control":
        payload.pop("control")
    elif mutation == "not_claimed":
        payload["not_claimed"] = []
    elif mutation == "positive":
        payload.pop("positive")
    elif mutation == "claim_capsule":
        (tmp_path / "reports/runs/d4/claim_capsule.json").unlink()
    if mutation in {"control", "not_claimed", "positive"}:
        _write_json(payload_path, payload)
    if mutation == "scorecard_hash":
        (tmp_path / "reports/canonical/quality-scorecard.json").unlink()
    elif mutation == "scorecard_ready":
        _write_json(tmp_path / "reports/canonical/quality-scorecard.json", _scorecard(status="not-ready"))

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "projected_discovery_required"
    if missing_key in {"scorecard_hash", "scorecard_ready"}:
        assert verdict["reason"] == "source-insufficient"
    else:
        assert verdict["reason"] == f"positive-acceptance-evidence-missing:{missing_key}"


def test_accepted_positive_happy_path_still_emits_positive_verdict(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "accepted_positive_discovery"
    assert verdict["reason"] == "discovery-level-D4-positive"


def test_positive_empirical_verdict_requires_owner_evidence_provenance(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    (tmp_path / "reports/canonical/index.json").unlink()

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "evidence-provenance-owner-missing"
    assert verdict["ledger_pointer"] == "reports/canonical/index.json:$.evidence_provenance"


def _add_high_impact_review(payload, *, bad_pointer=False):
    payload["review_owner"] = {"status": "complete"}
    payload["risk_ledger"] = {"status": "complete"}
    payload["external_validation"] = {"status": "complete"}
    payload["high_impact_claim_review"] = {
        "impact_domains": ["safety", "production", "real_model"],
        "scope_review_pointer": "reports/canonical/d4.json:$.review_owner",
        "risk_ledger_pointer": "reports/canonical/d4.json:$.risk_ledger",
        "external_validation_pointer": "reports/canonical/d4.json:$.external_validation",
    }
    if bad_pointer:
        payload["high_impact_claim_review"]["risk_ledger_pointer"] = "reports/canonical/d4.json:$.missing_risk_ledger"


def test_high_impact_positive_missing_review_preempts_acceptance(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload["positive"]["claim"] = "bounded safety fixture"
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "high-impact-review-required"
    assert verdict["ledger_pointer"] == "reports/canonical/d4.json:$.high_impact_claim_review"


def test_high_impact_positive_unresolved_review_pointer_preempts_acceptance(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    _add_high_impact_review(payload, bad_pointer=True)
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "high-impact-review-required"
    assert verdict["ledger_pointer"] == (
        "reports/canonical/d4.json:$.high_impact_claim_review.risk_ledger_pointer"
    )


def test_high_impact_positive_with_resolving_review_pointers_accepts(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    _add_high_impact_review(payload)
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "accepted_positive_discovery"
    assert verdict["reason"] == "discovery-level-D4-positive"


def _write_passing_dgt_hir(root):
    payload = {
        "schema_id": high_impact_review.SCHEMA_ID,
        "artifact_id": high_impact_review.ARTIFACT_ID,
        "generated_at": "2030-01-01T00:00:00+00:00",
        "seed": 1131,
        "source_artifacts": {
            "dgt": high_impact_review.DGT_ARTIFACT,
            "model_comparison": high_impact_review.MODEL_COMPARISON_ARTIFACT,
            "claim_graph": high_impact_review.CLAIM_GRAPH_ARTIFACT,
        },
        "review_rows": [
            {
                "claim_id": high_impact_review.DGT_CLAIM_ID,
                "status": "pass",
                "review_level": "bounded-D4-terminal-gate",
                "review_scope": "DGT bounded deterministic toy D4 positive-discovery terminal promotion only",
                "ledger_pointer": high_impact_review.DGT_REVIEW_ROW_POINTER,
                "claim_pointer": f"{high_impact_review.DGT_ARTIFACT}:$.d4_projection",
                "hardgate_pointer": f"{high_impact_review.JSON_ARTIFACT}:$.hardgates",
                "not_claimed_pointer": f"{high_impact_review.JSON_ARTIFACT}:$.not_claimed",
                "reason": "positive-discovery-gates-pass",
            }
        ],
        "hardgates": {
            f"HIR-HG{index}": {
                "status": "pass",
                "reason": "fixture",
                "evidence_pointer": f"{high_impact_review.DGT_ARTIFACT}:$.d4_projection",
            }
            for index in range(1, 11)
        },
        "not_claimed": list(high_impact_review.NOT_CLAIMED),
    }
    payload["hardgates"]["HIR-HG2"]["evidence_pointer"] = f"{high_impact_review.JSON_ARTIFACT}:$.not_claimed"
    payload["hardgates"]["HIR-HG6"]["evidence_pointer"] = f"{high_impact_review.DGT_ARTIFACT}:$.d4_projection"
    path = root / high_impact_review.JSON_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _dgt_fixture(tmp_path, monkeypatch):
    rows = [
        _discovery_row(
            "discovery-gated-transformer",
            high_impact_review.DGT_ARTIFACT,
            "D4",
            pointer="$.d4_projection",
        )
    ]
    specs = (
        _spec(
            "discovery-gated-transformer",
            high_impact_review.DGT_ARTIFACT,
            scope="$.d5_o_projection.scope",
            cost="$.architecture_spec",
            not_claimed="$.d5_o_projection.not_claimed",
            positive="$.d5_o_projection",
            control="$.d5_o_projection.evidence_pointers.stronger_matched_random",
        ),
    )
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / high_impact_review.DGT_ARTIFACT
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload.update(
        {
            "artifact_id": "bedc-quality-lab:discovery-gated-transformer",
            "model_id": "discovery-gated-transformer",
            "architecture_spec": {"status": "present"},
            "not_claimed": ["Bounded deterministic toy evidence only."],
            "positive_discovery": True,
            "net_positive_signal": True,
            "main_verdict": {
                "positive_discovery": True,
                "surface_delta_count": 1,
                "shift_information": 1,
                "structural_discovery": True,
                "net_positive_signal": True,
                "deltas": {"debt_delta": 0},
            },
            "evidence_basis": {
                "control_positive_discovery": False,
                "scorecard_ready": True,
                "audit_status": "valid",
                "net_positive_signal": True,
            },
            "matched_random_control": {"control_verdict": {"positive": False}},
            "scope_seal": VALID_SCOPE_SEAL,
            "d4_projection": {
                "discovery_level": "D4",
                "readiness": "ready",
                "positive_discovery": True,
                "net_positive_signal": True,
                "matched_control": {"control_positive": False},
                "failed_gate": None,
                "gates": {
                    f"PROJ-HG{index}": {"status": "pass"}
                    for index in range(1, 11)
                },
                "classifier_surface_delta_pointer": "$.tool_route_evidence.classifier_surface_delta",
                "forbidden_claim_term_audit": {"status": "pass"},
                "not_claimed": ["bounded D4 prototype only"],
                "scope_seal": VALID_SCOPE_SEAL,
            },
            "d5_o_projection": {
                "status": "blocked",
                "discovery_level": "D4",
                "source_level": "D4",
                "gate_status": "fail",
                "blocked_reason": "blocked-by-D5O-HG1",
                "not_claimed": [
                    "Bounded D5-O claim over deterministic toy surfaces only.",
                    "No production robustness claim.",
                    "No global robustness claim.",
                    "No LLM replacement claim.",
                ],
                "scope": {"claim": "bounded deterministic toy operational robustness"},
                "evidence_pointers": {"stronger_matched_random": "$.d5_o_projection.surface_summary.threshold_frontier.matched_random_pass_count"},
                "surface_summary": {"threshold_frontier": {"matched_random_pass_count": 0}},
            },
            "tool_route_evidence": {"classifier_surface_delta": {"status": "present"}},
        }
    )
    payload_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    return tmp_path


def test_dgt_d4_row_routes_through_generic_accepted_positive_path(tmp_path, monkeypatch):
    _dgt_fixture(tmp_path, monkeypatch)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:discovery-gated-transformer"
    assert verdict["claim_verdict"] == "projected_positive_discovery"
    assert verdict["reason"].startswith("fresh-discovery-level-D0:")
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].discovery_level"


def test_dgt_with_passing_high_impact_review_remains_owner_projection(tmp_path, monkeypatch):
    root = _dgt_fixture(tmp_path, monkeypatch)
    _write_passing_dgt_hir(root)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:discovery-gated-transformer"
    assert verdict["claim_verdict"] == "projected_positive_discovery"
    assert verdict["reason"].startswith("fresh-discovery-level-D0:")
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].discovery_level"


def test_dgt_blocked_d4_row_does_not_emit_d5_o_verdict(tmp_path, monkeypatch):
    _dgt_fixture(tmp_path, monkeypatch)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:discovery-gated-transformer"
    assert verdict["claim_verdict"] == "projected_positive_discovery"
    assert verdict["ledger_pointer"].endswith("$.rows[0].discovery_level")
    assert "D5-O" not in json.dumps(verdict, sort_keys=True)


def test_malformed_high_impact_review_does_not_affect_non_dgt(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    path = tmp_path / high_impact_review.JSON_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("{malformed\n", encoding="utf-8")

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_id"] == "claim:d4"
    assert verdict["claim_verdict"] == "accepted_positive_discovery"


def test_accepted_positive_accepts_no_control_rationale_pointer(tmp_path, monkeypatch):
    rows = [_discovery_row("d4", "reports/canonical/d4.json", "D4")]
    specs = (_spec("d4", "reports/canonical/d4.json", control=None, no_control_rationale="$.no_control_rationale"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/d4.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    payload.pop("control")
    _write_json(payload_path, payload)

    verdict = demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")[0]

    assert verdict["claim_verdict"] == "accepted_positive_discovery"
    assert verdict["reason"] == "discovery-level-D4-positive"


def test_dn_owner_without_what_was_learned_fails_through_owner_pointer(tmp_path, monkeypatch):
    rows = [_discovery_row("dn", "reports/canonical/dn.json", "DN")]
    specs = (_spec("dn", "reports/canonical/dn.json"),)
    _fixture_root(tmp_path, monkeypatch, rows, specs)
    payload_path = tmp_path / "reports/canonical/dn.json"
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    capsule = payload["claim_capsule_ref"]
    payload["claim_capsule"] = {"terminal_verdict": "DN(audit-improvement-tradeoff)"}
    payload["what_was_learned"] = ""
    _write_json(payload_path, payload)
    capsule_path = tmp_path / capsule
    capsule_payload = json.loads(capsule_path.read_text(encoding="utf-8"))
    capsule_payload["what_was_learned"] = ""
    _write_json(capsule_path, capsule_payload)
    rows[0]["failed_gate"] = "$.claim_capsule.terminal_verdict"
    _write_json(tmp_path / "reports/canonical/discovery_map.json", {"rows": rows})

    with pytest.raises(ValueError, match="DN discovery owner evidence missing: what_was_learned"):
        demo.compile_claim_verdicts(tmp_path, generated_at="2030-01-01T00:00:00+00:00")
