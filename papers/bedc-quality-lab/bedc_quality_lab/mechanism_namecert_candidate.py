"""Lab-local mechanism NameCert candidate ledger."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import asdict, dataclass, fields
from typing import Any, Mapping


SCOPE_SEAL = {
    "semantics": "lab-local MechanismNameCertCandidate",
    "formal_bedc_namecert": False,
    "lean_verification": False,
    "paper_closurestatus": False,
    "mechanism_theorem_closure": False,
    "not_claimed": [
        "not a formal BEDC NameCert",
        "not Lean verification",
        "not a paper closurestatus",
        "not mechanism theorem closure",
    ],
}


@dataclass(frozen=True)
class MechanismNameCertCandidate:
    name: str
    target_classifier: dict[str, Any]
    source_spec: dict[str, Any]
    mechanism_spec: dict[str, Any]
    intervention_spec: dict[str, Any]
    ablation_spec: dict[str, Any]
    stability_spec: dict[str, Any]
    ledger_policy: dict[str, Any]
    closure_status: dict[str, str]

    @classmethod
    def from_gap_head_sources(
        cls,
        *,
        a1_capsule: Mapping[str, Any],
        operational_payload: Mapping[str, Any] | None = None,
        ablation_payload: Mapping[str, Any] | None = None,
        robustness_payload: Mapping[str, Any] | None = None,
        stability_payload: Mapping[str, Any] | None = None,
    ) -> "MechanismNameCertCandidate":
        return from_gap_head_sources(
            a1_capsule=a1_capsule,
            operational_payload=operational_payload,
            ablation_payload=ablation_payload,
            robustness_payload=robustness_payload,
            stability_payload=stability_payload,
        )

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def from_gap_head_sources(
    *,
    a1_capsule: Mapping[str, Any],
    operational_payload: Mapping[str, Any] | None = None,
    ablation_payload: Mapping[str, Any] | None = None,
    robustness_payload: Mapping[str, Any] | None = None,
    stability_payload: Mapping[str, Any] | None = None,
) -> MechanismNameCertCandidate:
    mechanism_case = _mapping(a1_capsule.get("mechanism_case"))
    d5_o = _mapping(a1_capsule.get("d5_o"))
    d5_m = _mapping(a1_capsule.get("d5_m"))
    hardgates = _mapping(a1_capsule.get("hardgates"))
    gates = _mapping(hardgates.get("gates"))
    a4_hardgates = _mapping(a1_capsule.get("a4_hardgates"))
    a4_gates = _mapping(a4_hardgates.get("gates"))
    a4_hg5 = _mapping(a4_gates.get("A4-HG5"))
    residualized_attribution = _mapping(a1_capsule.get("residualized_attribution"))
    score_margin_causal_evidence = _mapping(a1_capsule.get("score_margin_causal_evidence"))

    candidate_mechanism = _candidate_mechanism(mechanism_case)
    full_vs_score_plus_margin = _full_vs_score_plus_margin(gates, mechanism_case)
    canonical_source_status = "present" if a1_capsule else "missing"
    a4_pointer_present = bool(residualized_attribution and score_margin_causal_evidence and a4_hg5)

    target_classifier = {
        "name": "gap-head-on-h",
        "operational_level": "D5-O" if d5_o.get("status") == "ready" else "missing",
        "operational_source_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.d5_o",
    }
    source_spec = {
        "scope_seal": deepcopy(SCOPE_SEAL),
        "canonical_source": {
            "artifact_id": a1_capsule.get("artifact_id", "gap_head_attribution_capsule"),
            "json_artifact": "reports/canonical/gap_head_attribution_capsule.json",
            "run_id": a1_capsule.get("run_id"),
            "status": canonical_source_status,
        },
        "optional_sources": {
            "operational": _source_cell(operational_payload, "reports/canonical/gap-head-on-h.json"),
            "ablation": _source_cell(ablation_payload, "reports/canonical/gap-head-ablation.json"),
            "robustness": _source_cell(robustness_payload, "reports/canonical/gap-head-robustness-sweep.json"),
            "stability": _source_cell(stability_payload, "reports/gap_head_discovery_stability.json"),
        },
    }
    mechanism_spec = {
        "candidate_mechanism": candidate_mechanism,
        "full_vs_score_plus_margin": full_vs_score_plus_margin,
        "a1_mechanism_case": mechanism_case.get("case", "missing"),
        "a1_mechanism_status": mechanism_case.get("status", "missing"),
        "a1_failed_gate": hardgates.get("failed_gate") or d5_m.get("failed_gate"),
        "a1_d5_m_status": d5_m.get("status", "missing"),
        "a1_d5_m_passed": bool(d5_m.get("passed") is True),
        "source_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_case",
        "a4_gate_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5",
        "residualized_attribution_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution",
        "score_margin_causal_evidence_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence",
        "a4_d5_m_passed": bool(a4_hg5.get("status") == "pass"),
        "a4_pointer_present": a4_pointer_present,
    }
    intervention_spec = _intervention_spec(operational_payload)
    ablation_spec = _ablation_spec(ablation_payload, robustness_payload)
    stability_spec = _stability_spec(robustness_payload, stability_payload)
    closure_status = _closure_status(
        mechanism_spec=mechanism_spec,
        intervention_spec=intervention_spec,
        ablation_spec=ablation_spec,
        stability_spec=stability_spec,
    )
    closure_status["source_spec"] = "closed" if canonical_source_status == "present" else "partial"
    ledger_policy = _ledger_policy(mechanism_spec=mechanism_spec, closure_status=closure_status)
    closure_status["ledger_policy"] = "closed" if ledger_policy["mechanism_closure_debt"] == "closed" else "open"

    return MechanismNameCertCandidate(
        name="MechanismNameCertCandidate:gap-head-on-h",
        target_classifier=target_classifier,
        source_spec=source_spec,
        mechanism_spec=mechanism_spec,
        intervention_spec=intervention_spec,
        ablation_spec=ablation_spec,
        stability_spec=stability_spec,
        ledger_policy=ledger_policy,
        closure_status=closure_status,
    )


def closure_status_rows(candidate: MechanismNameCertCandidate) -> list[dict[str, str]]:
    return [
        {
            "field": field.name,
            "status": candidate.closure_status.get(field.name, "present"),
            "pointer": f"$.{field.name}",
        }
        for field in fields(candidate)
        if field.name != "closure_status"
    ] + [
        {
            "field": "closure_status",
            "status": "closed" if _scope_seal_closed(candidate.source_spec) else "partial",
            "pointer": "$.closure_status",
        }
    ]


def audit_mechanism_namecert_candidate(payload: Mapping[str, Any]) -> dict[str, Any]:
    scope_seal = _mapping(_mapping(payload.get("source_spec")).get("scope_seal"))
    ledger_policy = _mapping(payload.get("ledger_policy"))
    closure_status = _mapping(payload.get("closure_status"))
    mechanism_spec = _mapping(payload.get("mechanism_spec"))
    scope_pass = _scope_seal_closed({"scope_seal": scope_seal})
    d5_m_ready = (
        ledger_policy.get("mechanism_closure_debt") == "closed"
        and closure_status.get("mechanism_spec") == "closed"
    )
    required = {
        "$.ledger_policy.mechanism_closure_debt": ledger_policy.get("mechanism_closure_debt"),
        "$.closure_status.mechanism_spec": closure_status.get("mechanism_spec"),
        "$.mechanism_spec.candidate_mechanism": mechanism_spec.get("candidate_mechanism"),
        "$.mechanism_spec.full_vs_score_plus_margin": mechanism_spec.get("full_vs_score_plus_margin"),
    }
    missing = [pointer for pointer, value in required.items() if value is None]
    return {
        "status": "pass" if scope_pass and not missing else "fail",
        "scope_seal": "closed" if scope_pass else "partial",
        "d5_m_ready": bool(d5_m_ready),
        "required_pointers": required,
        "missing_required_pointers": missing,
    }


def render_mechanism_namecert_markdown(payload: Mapping[str, Any]) -> str:
    audit = audit_mechanism_namecert_candidate(payload)
    lines = [
        "# Gap-Head MechanismNameCert Candidate",
        "",
        f"- Artifact: `{payload.get('artifact_id', 'bedc-quality-lab:gap-head-mechanism-namecert')}`",
        f"- JSON: `{payload.get('json_artifact', 'reports/gap_head_mechanism_namecert.json')}`",
        f"- Candidate: `{payload.get('name', 'missing')}`",
        f"- Target classifier: `{_mapping(payload.get('target_classifier')).get('name', 'missing')}`",
        f"- Candidate mechanism: `{_mapping(payload.get('mechanism_spec')).get('candidate_mechanism', 'missing')}`",
        f"- Full vs score plus margin: `{_mapping(payload.get('mechanism_spec')).get('full_vs_score_plus_margin', 'missing')}`",
        f"- Mechanism closure debt: `{_mapping(payload.get('ledger_policy')).get('mechanism_closure_debt', 'missing')}`",
        f"- Mechanism spec closure: `{_mapping(payload.get('closure_status')).get('mechanism_spec', 'missing')}`",
        "- Mechanism ledger pointer: `$.ledger_policy.mechanism_closure_debt`",
        "- Mechanism closure pointer: `$.closure_status.mechanism_spec`",
        f"- D5-M ready: `{audit['d5_m_ready']}`",
        "",
        "## Scope Seal",
        "",
    ]
    for item in _mapping(_mapping(payload.get("source_spec")).get("scope_seal")).get("not_claimed", []):
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Closure Rows",
            "",
            "| field | status | pointer |",
            "| --- | --- | --- |",
        ]
    )
    candidate = _candidate_from_payload(payload)
    for row in closure_status_rows(candidate):
        lines.append(f"| `{row['field']}` | `{row['status']}` | `{row['pointer']}` |")
    lines.append("")
    return "\n".join(lines)


def _candidate_from_payload(payload: Mapping[str, Any]) -> MechanismNameCertCandidate:
    return MechanismNameCertCandidate(
        name=str(payload.get("name", "missing")),
        target_classifier=dict(_mapping(payload.get("target_classifier"))),
        source_spec=dict(_mapping(payload.get("source_spec"))),
        mechanism_spec=dict(_mapping(payload.get("mechanism_spec"))),
        intervention_spec=dict(_mapping(payload.get("intervention_spec"))),
        ablation_spec=dict(_mapping(payload.get("ablation_spec"))),
        stability_spec=dict(_mapping(payload.get("stability_spec"))),
        ledger_policy=dict(_mapping(payload.get("ledger_policy"))),
        closure_status={str(key): str(value) for key, value in _mapping(payload.get("closure_status")).items()},
    )


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _candidate_mechanism(mechanism_case: Mapping[str, Any]) -> str:
    explicit = mechanism_case.get("candidate_mechanism")
    if explicit in {"probe-margin-channel", "mixed-score-margin-channel", "closed-attribution", "unresolved"}:
        return str(explicit)
    status = mechanism_case.get("status")
    if isinstance(status, str) and "mechanism = probe-margin-channel" in status:
        return "probe-margin-channel"
    if isinstance(status, str) and "D5-M candidate" in status:
        return "closed-attribution"
    if isinstance(status, str) and "scale/norm detector" in status:
        return "scale-norm-detector"
    return "unresolved"


def _full_vs_score_plus_margin(gates: Mapping[str, Any], mechanism_case: Mapping[str, Any]) -> str:
    gate = _mapping(gates.get("A1-HG3"))
    if gate.get("status") == "pass":
        return "separated"
    learned = mechanism_case.get("what_was_learned")
    if isinstance(learned, str) and "score_plus_margin remains statistically competitive with full" in learned:
        return "not separated"
    return "not separated" if gate else "missing"


def _source_cell(payload: Mapping[str, Any] | None, artifact: str) -> dict[str, str]:
    if payload is None:
        return {"artifact": artifact, "status": "missing"}
    return {"artifact": artifact, "status": "present"}


def _intervention_spec(payload: Mapping[str, Any] | None) -> dict[str, Any]:
    if payload is None:
        return {"status": "missing", "source_pointer": "reports/canonical/gap-head-on-h.json"}
    treatment = _mapping(payload.get("treatment_verdict"))
    control = _mapping(payload.get("control_verdict"))
    closed = treatment.get("positive") is True and control.get("positive") is False
    return {
        "status": "closed" if closed else "partial",
        "treatment_pointer": "reports/canonical/gap-head-on-h.json:$.treatment_verdict.positive",
        "control_pointer": "reports/canonical/gap-head-on-h.json:$.control_verdict.positive",
    }


def _ablation_spec(
    ablation_payload: Mapping[str, Any] | None,
    robustness_payload: Mapping[str, Any] | None,
) -> dict[str, Any]:
    ablation_status = _mapping(ablation_payload.get("hardgate")).get("status") if ablation_payload is not None else None
    robustness_status = _mapping(robustness_payload.get("A2_feature_ablation")).get("status") if robustness_payload is not None else None
    closed = ablation_payload is not None and robustness_status == "complete"
    return {
        "status": "closed" if closed else "partial" if ablation_status or robustness_status else "missing",
        "ablation_pointer": "reports/canonical/gap-head-ablation.json:$.hardgate.status",
        "robustness_ablation_pointer": "reports/canonical/gap-head-robustness-sweep.json:$.A2_feature_ablation.status",
        "source_status": ablation_status or "missing",
        "robustness_status": robustness_status or "missing",
    }


def _stability_spec(
    robustness_payload: Mapping[str, Any] | None,
    stability_payload: Mapping[str, Any] | None,
) -> dict[str, Any]:
    seed_status = _mapping(robustness_payload.get("A3_seed_expansion")).get("final_verdict") if robustness_payload is not None else None
    stability_status = stability_payload.get("final_verdict") if stability_payload is not None else None
    closed = seed_status == "robust_positive" and isinstance(stability_status, str)
    return {
        "status": "closed" if closed else "partial" if seed_status or stability_status else "missing",
        "seed_expansion_pointer": "reports/canonical/gap-head-robustness-sweep.json:$.A3_seed_expansion.final_verdict",
        "stability_pointer": "reports/gap_head_discovery_stability.json:$.final_verdict",
        "seed_expansion_status": seed_status or "missing",
        "stability_status": stability_status or "missing",
    }


def _closure_status(
    *,
    mechanism_spec: Mapping[str, Any],
    intervention_spec: Mapping[str, Any],
    ablation_spec: Mapping[str, Any],
    stability_spec: Mapping[str, Any],
) -> dict[str, str]:
    mechanism_closed = (
        mechanism_spec.get("candidate_mechanism") != "probe-margin-channel"
        and mechanism_spec.get("a1_d5_m_passed") is True
        and mechanism_spec.get("a4_d5_m_passed") is True
        and mechanism_spec.get("a4_pointer_present") is True
    )
    return {
        "target_classifier": "closed",
        "source_spec": "closed",
        "mechanism_spec": "closed" if mechanism_closed else "partial",
        "intervention_spec": _status_cell(intervention_spec),
        "ablation_spec": _status_cell(ablation_spec),
        "stability_spec": _status_cell(stability_spec),
    }


def _ledger_policy(mechanism_spec: Mapping[str, Any], closure_status: Mapping[str, str]) -> dict[str, Any]:
    mechanism_closed = closure_status.get("mechanism_spec") == "closed"
    debt = "closed" if mechanism_closed else "open"
    blockers: list[str] = []
    if mechanism_spec.get("candidate_mechanism") == "probe-margin-channel":
        blockers.append("probe-margin-channel")
    if mechanism_spec.get("full_vs_score_plus_margin") == "not separated":
        blockers.append("full_vs_score_plus_margin")
    if mechanism_spec.get("a4_d5_m_passed") is not True:
        blockers.extend(["A4-HG1", "A4-HG2", "A4-HG3", "A4-HG4", "A4-HG5"])
    if not mechanism_spec.get("residualized_attribution_pointer"):
        blockers.append("residualized_attribution")
    if not mechanism_spec.get("score_margin_causal_evidence_pointer"):
        blockers.append("score_margin_causal_evidence")
    if mechanism_spec.get("a4_pointer_present") is not True:
        for blocker in ("residualized_attribution", "score_margin_causal_evidence"):
            if blocker not in blockers:
                blockers.append(blocker)
    if not mechanism_closed and not blockers:
        blockers.append("mechanism_spec")
    return {
        "mechanism_closure_debt": debt,
        "d5_m_ready_policy": "requires closed ledger_policy.mechanism_closure_debt and closed closure_status.mechanism_spec",
        "blocking_cells": blockers,
        "ledger_pointer": "$.ledger_policy.mechanism_closure_debt",
        "closure_pointer": "$.closure_status.mechanism_spec",
    }


def _status_cell(spec: Mapping[str, Any]) -> str:
    status = spec.get("status")
    return status if status in {"closed", "partial", "missing"} else "partial"


def _scope_seal_closed(source_spec: Mapping[str, Any]) -> bool:
    seal = _mapping(source_spec.get("scope_seal"))
    return (
        seal.get("semantics") == "lab-local MechanismNameCertCandidate"
        and seal.get("formal_bedc_namecert") is False
        and seal.get("lean_verification") is False
        and seal.get("paper_closurestatus") is False
        and seal.get("mechanism_theorem_closure") is False
        and bool(seal.get("not_claimed"))
    )
