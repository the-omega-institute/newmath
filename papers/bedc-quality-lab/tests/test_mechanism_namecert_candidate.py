import json
from dataclasses import fields

from bedc_quality_lab import __all__ as package_all
from bedc_quality_lab.mechanism_namecert_candidate import (
    MechanismNameCertCandidate,
    audit_mechanism_namecert_candidate,
    closure_status_rows,
)


def _a1_capsule(*, candidate="probe-margin-channel", separated="not separated"):
    status = "D5-O retained, mechanism = probe-margin-channel" if candidate == "probe-margin-channel" else "D5-M candidate"
    return {
        "artifact_id": "gap_head_attribution_capsule",
        "run_id": "fixture",
        "mechanism_case": {
            "case": "Case 2" if candidate == "probe-margin-channel" else "Case 1",
            "status": status,
            "failed_gate": "A1-HG3" if separated == "not separated" else None,
            "what_was_learned": "score_plus_margin remains statistically competitive with full."
            if separated == "not separated"
            else "full exceeds score_plus_margin and h_norm_only under the predeclared CI gates.",
        },
        "d5_o": {"status": "ready"},
        "d5_m": {"status": "blocked" if separated == "not separated" else "ready", "passed": separated == "separated", "failed_gate": "A1-HG3" if separated == "not separated" else None},
        "hardgates": {"gates": {"A1-HG3": {"status": "fail" if separated == "not separated" else "pass"}}},
    }


def test_exact_field_shape_json_ready_and_package_local():
    candidate = MechanismNameCertCandidate.from_gap_head_sources(a1_capsule=_a1_capsule())
    payload = candidate.to_dict()

    assert [field.name for field in fields(MechanismNameCertCandidate)] == [
        "name",
        "target_classifier",
        "source_spec",
        "mechanism_spec",
        "intervention_spec",
        "ablation_spec",
        "stability_spec",
        "ledger_policy",
        "closure_status",
    ]
    assert "MechanismNameCertCandidate" not in package_all
    assert json.loads(json.dumps(payload))["name"] == "MechanismNameCertCandidate:gap-head-on-h"


def test_scope_seal_and_required_pointers_are_explicit():
    candidate = MechanismNameCertCandidate.from_gap_head_sources(a1_capsule=_a1_capsule())
    payload = candidate.to_dict()
    seal = payload["source_spec"]["scope_seal"]
    audit = audit_mechanism_namecert_candidate(payload)

    assert seal["semantics"] == "lab-local MechanismNameCertCandidate"
    assert seal["formal_bedc_namecert"] is False
    assert seal["lean_verification"] is False
    assert seal["paper_closurestatus"] is False
    assert seal["mechanism_theorem_closure"] is False
    assert audit["status"] == "pass"
    assert "$.ledger_policy.mechanism_closure_debt" in audit["required_pointers"]
    assert "$.closure_status.mechanism_spec" in audit["required_pointers"]
    assert "$.mechanism_spec.candidate_mechanism" in audit["required_pointers"]
    assert "$.mechanism_spec.full_vs_score_plus_margin" in audit["required_pointers"]


def test_probe_margin_channel_blocks_mechanism_closure():
    candidate = MechanismNameCertCandidate.from_gap_head_sources(a1_capsule=_a1_capsule())

    assert candidate.mechanism_spec["candidate_mechanism"] == "probe-margin-channel"
    assert candidate.mechanism_spec["full_vs_score_plus_margin"] == "not separated"
    assert candidate.closure_status["mechanism_spec"] == "partial"
    assert candidate.ledger_policy["mechanism_closure_debt"] == "open"
    assert audit_mechanism_namecert_candidate(candidate.to_dict())["d5_m_ready"] is False


def test_closed_d5_m_requires_closed_ledger_and_closed_mechanism_spec():
    candidate = MechanismNameCertCandidate.from_gap_head_sources(
        a1_capsule=_a1_capsule(candidate="closed-attribution", separated="separated")
    )
    rows = {row["field"]: row for row in closure_status_rows(candidate)}

    assert candidate.closure_status["mechanism_spec"] == "closed"
    assert candidate.ledger_policy["mechanism_closure_debt"] == "closed"
    assert rows["mechanism_spec"]["status"] == "closed"
    assert audit_mechanism_namecert_candidate(candidate.to_dict())["d5_m_ready"] is True
