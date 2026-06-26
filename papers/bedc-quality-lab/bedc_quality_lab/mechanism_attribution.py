"""Typed projector for gap-head attribution capsule mechanism evidence."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import pointer_value


ATTRIBUTION_CAPSULE_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"
MECHANISM_EVIDENCE_POINTER = "$.mechanism_evidence"
MECHANISM_EVIDENCE_LEVEL_POINTER = "$.mechanism_evidence.evidence_level"
CAUSAL_EVIDENCE_LEVELS = ("observational", "ablation", "patch", "intervention", "counterfactual")
D5_M_CAUSAL_EVIDENCE_LEVELS = ("patch", "intervention", "counterfactual")


@dataclass(frozen=True)
class MechanismAttributionEvidence:
    evidence_level: str
    base_level: str
    base_status: str
    mechanism_level: str
    mechanism_status: str
    candidate_mechanism: str
    failed_gate: str | None
    residualized_significant: bool
    control_clear: bool
    score_margin_sufficient: bool
    required_gate_pointers: tuple[str, ...]
    metric_pointers: dict[str, str]
    ledger_debt_pointer: str
    closure_pointer: str
    source_issue: int | None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @property
    def mechanism_pointer(self) -> str:
        return MECHANISM_EVIDENCE_POINTER

    @property
    def mechanism_case_pointer(self) -> str:
        return f"{MECHANISM_EVIDENCE_POINTER}.candidate_mechanism"


def project_gap_head_mechanism_evidence(
    payload: Mapping[str, Any],
) -> MechanismAttributionEvidence | None:
    evidence = _mapping(payload.get("mechanism_evidence"))
    if not evidence:
        return None
    required_gate_pointers = _string_tuple(evidence.get("required_gate_pointers"))
    metric_pointers = _string_mapping(evidence.get("metric_pointers"))
    base_level = evidence.get("base_level")
    base_status = evidence.get("base_status")
    mechanism_level = evidence.get("mechanism_level")
    mechanism_status = evidence.get("mechanism_status")
    candidate = evidence.get("candidate_mechanism")
    evidence_level = evidence.get("evidence_level")
    ledger_debt_pointer = evidence.get("ledger_debt_pointer")
    closure_pointer = evidence.get("closure_pointer")
    if not all(
        isinstance(value, str) and value
        for value in (
            evidence_level,
            base_level,
            base_status,
            mechanism_level,
            mechanism_status,
            candidate,
            ledger_debt_pointer,
            closure_pointer,
        )
    ):
        return None
    if evidence_level not in CAUSAL_EVIDENCE_LEVELS:
        return None
    if not required_gate_pointers or not metric_pointers:
        return None
    source_issue = evidence.get("source_issue")
    return MechanismAttributionEvidence(
        evidence_level=str(evidence_level),
        base_level=str(base_level),
        base_status=str(base_status),
        mechanism_level=str(mechanism_level),
        mechanism_status=str(mechanism_status),
        candidate_mechanism=str(candidate),
        failed_gate=evidence.get("failed_gate") if isinstance(evidence.get("failed_gate"), str) else None,
        residualized_significant=bool(evidence.get("residualized_significant") is True),
        control_clear=bool(evidence.get("control_clear") is True),
        score_margin_sufficient=bool(evidence.get("score_margin_sufficient") is True),
        required_gate_pointers=required_gate_pointers,
        metric_pointers=metric_pointers,
        ledger_debt_pointer=str(ledger_debt_pointer),
        closure_pointer=str(closure_pointer),
        source_issue=int(source_issue) if isinstance(source_issue, int) and not isinstance(source_issue, bool) else None,
    )


def mechanism_evidence_pointers(evidence: MechanismAttributionEvidence) -> tuple[str, ...]:
    return (
        MECHANISM_EVIDENCE_LEVEL_POINTER,
        *evidence.required_gate_pointers,
        *tuple(evidence.metric_pointers.values()),
        evidence.ledger_debt_pointer,
        evidence.closure_pointer,
    )


def mechanism_causal_evidence_ready(evidence: MechanismAttributionEvidence | None) -> bool:
    return evidence is not None and evidence.evidence_level in D5_M_CAUSAL_EVIDENCE_LEVELS


def unresolved_mechanism_evidence_pointers(
    payload: Mapping[str, Any],
    evidence: MechanismAttributionEvidence,
) -> tuple[str, ...]:
    return tuple(pointer for pointer in mechanism_evidence_pointers(evidence) if pointer_value(payload, pointer) is None)


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _string_tuple(value: Any) -> tuple[str, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        return ()
    return tuple(str(item) for item in value if isinstance(item, str) and item)


def _string_mapping(value: Any) -> dict[str, str]:
    if not isinstance(value, Mapping):
        return {}
    return {str(key): str(cell) for key, cell in value.items() if isinstance(key, str) and isinstance(cell, str) and cell}
