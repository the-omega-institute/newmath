import json
from dataclasses import fields

from bedc_quality_lab import __all__ as package_all
from bedc_quality_lab.mechanism_namecert_candidate import (
    MechanismNameCertCandidate,
    audit_mechanism_namecert_candidate,
    closure_status_rows,
)


def _a1_capsule(*, candidate="probe-margin-channel", separated="not separated", a4_pass=False, classification="score_margin_sufficient"):
    status = "D5-O retained, mechanism = probe-margin-channel" if candidate == "probe-margin-channel" else "D5-M candidate"
    failed_gate = None if a4_pass and separated == "separated" else "A4-HG5"
    mechanism_status = "ready" if a4_pass and separated == "separated" else "blocked"
    payload = {
        "artifact_id": "gap_head_attribution_capsule",
        "run_id": "fixture",
        "source_issues": [692, 747],
        "mechanism_case": {
            "case": "Case B" if candidate == "probe-margin-channel" else "Case C",
            "status": status,
            "failed_gate": failed_gate,
            "candidate_mechanism": candidate,
            "what_was_learned": "score_plus_margin remains statistically competitive with full."
            if separated == "not separated"
            else "residualized attribution remains strong and score/margin is not sufficient.",
        },
        "d5_o": {"status": "ready"},
        "d5_m": {"status": mechanism_status, "passed": mechanism_status == "ready", "failed_gate": failed_gate},
        "hardgates": {"gates": {"A1-HG3": {"status": "fail" if separated == "not separated" else "pass"}}},
        "a4_hardgates": {
            "gates": {
                "A4-HG2": {"status": "pass"},
                "A4-HG3": {"status": "pass"},
                "A4-HG5": {"status": "pass" if a4_pass else "fail"},
            }
        },
        "residualized_attribution": {"status": "pass"},
        "score_margin_causal_evidence": {"channel_classification": classification},
    }
    payload["mechanism_evidence"] = {
        "base_level": "D5-O",
        "base_status": "ready",
        "mechanism_level": "D5-M" if mechanism_status == "ready" else "blocked",
        "mechanism_status": mechanism_status,
        "candidate_mechanism": candidate,
        "failed_gate": failed_gate,
        "residualized_significant": True,
        "control_clear": True,
        "score_margin_sufficient": classification == "score_margin_sufficient",
        "required_gate_pointers": [
            "$.a4_hardgates.gates.A4-HG2.status",
            "$.a4_hardgates.gates.A4-HG3.status",
            "$.a4_hardgates.gates.A4-HG5.status",
        ],
        "metric_pointers": {
            "residualized_status": "$.residualized_attribution.status",
            "score_margin_channel_classification": "$.score_margin_causal_evidence.channel_classification",
        },
        "ledger_debt_pointer": "$.ledger_debt.0.status",
        "closure_pointer": "$.mechanism_evidence.mechanism_status",
        "source_issue": 747,
    }
    payload["ledger_debt"] = [{"debt_id": "gap-head-mechanism-evidence-closure", "status": "closed" if mechanism_status == "ready" else "open"}]
    payload["not_implemented"] = ["nonlinear_residualization", "full_causal_replacement_scope"]
    return payload


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
        a1_capsule=_a1_capsule(candidate="closed-attribution", separated="separated", a4_pass=True, classification="not_score_margin_sufficient")
    )
    rows = {row["field"]: row for row in closure_status_rows(candidate)}

    assert candidate.closure_status["mechanism_spec"] == "closed"
    assert candidate.ledger_policy["mechanism_closure_debt"] == "closed"
    assert rows["mechanism_spec"]["status"] == "closed"
    assert audit_mechanism_namecert_candidate(candidate.to_dict())["d5_m_ready"] is True


def test_a1_only_d5_m_evidence_cannot_close_without_a4_hg5():
    capsule = _a1_capsule(candidate="closed-attribution", separated="separated", a4_pass=True, classification="not_score_margin_sufficient")
    capsule["d5_m"] = {"status": "ready", "passed": True, "failed_gate": None}
    capsule.pop("mechanism_evidence")

    candidate = MechanismNameCertCandidate.from_gap_head_sources(a1_capsule=capsule)

    assert candidate.mechanism_spec["a1_d5_m_passed"] is False
    assert candidate.mechanism_spec["a4_d5_m_passed"] is False
    assert candidate.closure_status["mechanism_spec"] == "partial"
    assert candidate.ledger_policy["mechanism_closure_debt"] == "open"
    assert "A4-HG5" in candidate.ledger_policy["blocking_cells"]
