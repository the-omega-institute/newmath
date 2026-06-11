"""Single owner for construct-validity hardgates."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc.quality.construct_validity_hardgates"
ARTIFACT_ID = "bedc-quality-lab:construct-validity-hardgates"
OWNER_MODULE = "bedc_quality_lab/construct_validity.py"
OWNER_POINTER = "bedc_quality_lab.construct_validity:evaluate_construct_validity"
GATE_IDS = ("CV-HG1", "CV-HG2", "CV-HG3", "CV-HG4", "CV-HG5")
CLAIM_CAPSULE_PROJECTION_KEYS = ("artifact", "pointer", "status", "failed_gates", "owner_pointer")


@dataclass(frozen=True)
class ConstructValidityEvidence:
    task_variables: Any
    label_variables: Any
    arm_input_access: Any
    arm_roles: Any
    finite_table: Any
    hand_feature_ledger: Any
    metric_source: Any

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any] | "ConstructValidityEvidence") -> "ConstructValidityEvidence":
        if isinstance(payload, ConstructValidityEvidence):
            return payload
        required = (
            "task_variables",
            "label_variables",
            "arm_input_access",
            "arm_roles",
            "finite_table",
            "hand_feature_ledger",
            "metric_source",
        )
        return cls(**{key: payload.get(key) for key in required})

    def as_payload(self) -> dict[str, Any]:
        return {
            "task_variables": self.task_variables,
            "label_variables": self.label_variables,
            "arm_input_access": self.arm_input_access,
            "arm_roles": self.arm_roles,
            "finite_table": self.finite_table,
            "hand_feature_ledger": self.hand_feature_ledger,
            "metric_source": self.metric_source,
        }


@dataclass(frozen=True)
class ConstructValidityAudit:
    status: str
    failed_gates: tuple[str, ...]
    gates: Mapping[str, Mapping[str, Any]]
    claim_capsule_projection: Mapping[str, Any]
    owner_pointer: str = OWNER_POINTER

    def claim_capsule_projection_for(self, *, artifact: str, pointer: str) -> dict[str, Any]:
        return {
            "artifact": artifact,
            "pointer": pointer,
            "status": self.status,
            "failed_gates": list(self.failed_gates),
            "owner_pointer": self.owner_pointer,
        }

    def as_payload(self, *, artifact: str | None = None, pointer: str = "$") -> dict[str, Any]:
        projection = (
            self.claim_capsule_projection_for(artifact=artifact, pointer=pointer)
            if artifact is not None
            else dict(self.claim_capsule_projection)
        )
        return {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "owner_module": OWNER_MODULE,
            "owner_pointer": self.owner_pointer,
            "status": self.status,
            "failed_gates": list(self.failed_gates),
            "gates": {gate_id: dict(row) for gate_id, row in self.gates.items()},
            "claim_capsule_projection": projection,
        }


def _is_mapping(value: Any) -> bool:
    return isinstance(value, Mapping)


def _is_sequence(value: Any) -> bool:
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray))


def _variables(value: Any, *keys: str) -> tuple[str, ...]:
    if value is None:
        return ()
    if _is_mapping(value):
        search_keys = keys or ("variables", "task_variables", "label_variables", "labels")
        for key in search_keys:
            cell = value.get(key)
            if _is_sequence(cell):
                return tuple(str(item) for item in cell if str(item))
        if all(isinstance(key, str) for key in value.keys()) and all(isinstance(cell, bool) for cell in value.values()):
            return tuple(str(key) for key, present in value.items() if present)
        return ()
    if _is_sequence(value):
        return tuple(str(item) for item in value if str(item))
    return ()


def _mapping(value: Any, key: str | None = None) -> Mapping[str, Any]:
    if not _is_mapping(value):
        return {}
    if key is None:
        return value
    cell = value.get(key)
    return cell if _is_mapping(cell) else {}


def _list_cell(value: Any) -> tuple[Any, ...]:
    if _is_sequence(value):
        return tuple(value)
    if value in (None, ""):
        return ()
    return (value,)


def _bool_cell(value: Any, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    if isinstance(value, str):
        lowered = value.strip().lower()
        if lowered in {"true", "yes", "pass", "present"}:
            return True
        if lowered in {"false", "no", "fail", "missing"}:
            return False
    return bool(value)


def _number_cell(value: Any) -> float | None:
    try:
        result = float(value)
    except (TypeError, ValueError):
        return None
    return result


def _gate(
    gate_id: str,
    *,
    status: str,
    criterion: str,
    evidence_pointer: str,
    reason: str | None = None,
    **extra: Any,
) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": status,
        "criterion": criterion,
        "evidence_pointer": evidence_pointer,
        "reason": reason,
        **extra,
    }


def _gate_cv_hg1(evidence: ConstructValidityEvidence) -> dict[str, Any]:
    task_vars = set(_variables(evidence.task_variables, "variables", "task_variables"))
    label_vars = set(_variables(evidence.label_variables, "variables", "label_variables", "labels"))
    roles = _mapping(evidence.arm_roles)
    controls = roles.get("controls")
    candidate = roles.get("candidate") or roles.get("candidate_arm")
    role_map = _mapping(roles, "roles")
    has_roles = bool(candidate and _is_sequence(controls) and controls) or (
        role_map and "candidate" in set(str(role) for role in role_map.values()) and "control" in set(str(role) for role in role_map.values())
    )
    overlap = sorted(task_vars.intersection(label_vars))
    ok = bool(task_vars) and bool(label_vars) and has_roles and not overlap
    return _gate(
        "CV-HG1",
        status="pass" if ok else "fail",
        criterion="task variables, label variables, candidate arm, and control arm roles are declared without variable aliasing",
        evidence_pointer="$.construct_validity_hardgates.evidence.task_variables",
        reason=None if ok else "missing task/label/role declaration or aliased task and label variables",
        task_variable_count=len(task_vars),
        label_variable_count=len(label_vars),
        aliased_variables=overlap,
    )


def _arm_access(value: Any) -> Mapping[str, Any]:
    if not _is_mapping(value):
        return {}
    arms = value.get("arms")
    return arms if _is_mapping(arms) else value


def _gate_cv_hg2(evidence: ConstructValidityEvidence) -> dict[str, Any]:
    labels = set(_variables(evidence.label_variables, "variables", "label_variables", "labels"))
    access_root = _mapping(evidence.arm_input_access)
    arms = _arm_access(access_root)
    visible: dict[str, list[str]] = {}
    for arm_id, cell in arms.items():
        if str(arm_id) in {"status", "label_invisibility_certificate", "certificate_pointer"}:
            continue
        variables = set(_variables(cell, "variables", "inputs", "accessible_variables"))
        leaked = sorted(variables.intersection(labels))
        if leaked:
            visible[str(arm_id)] = leaked
    certificate = _bool_cell(access_root.get("label_invisibility_certificate"), default=False)
    ok = bool(labels) and bool(arms) and certificate and not visible
    return _gate(
        "CV-HG2",
        status="pass" if ok else "fail",
        criterion="label variables are absent from all arm input-access declarations",
        evidence_pointer="$.construct_validity_hardgates.evidence.arm_input_access",
        reason=None if ok else "label variable is visible to an arm or no invisibility certificate is present",
        visible_label_variables=visible,
        label_invisibility_certificate=certificate,
    )


def _gate_cv_hg3(evidence: ConstructValidityEvidence) -> dict[str, Any]:
    table = _mapping(evidence.finite_table)
    support_count = _number_cell(table.get("support_count", table.get("pair_count", table.get("cell_count"))))
    coverage_status = str(table.get("coverage_status", table.get("status", ""))).strip()
    rule_claim = _bool_cell(table.get("rule_abstraction_claim"), default=False)
    table_only = _bool_cell(table.get("table_coverage_only"), default=False)
    finite_accuracy = _number_cell(table.get("finite_pair_accuracy", table.get("plateau_accuracy")))
    abstraction_basis = str(table.get("abstraction_basis", "")).strip()
    extrapolation = _bool_cell(table.get("extrapolation_splits"), default=False)
    plateau = finite_accuracy is not None and finite_accuracy >= 0.98 and rule_claim and not extrapolation
    table_coverage_statuses = {"table-coverage", "finite-table-only", "bounded-table-only"}
    if not table or support_count is None or support_count <= 0:
        status = "fail"
        reason = "finite table coverage evidence is missing"
    elif table_only or coverage_status in table_coverage_statuses or plateau:
        status = "table-coverage"
        reason = "finite table coverage cannot support a rule-abstraction claim"
    else:
        ok = (not rule_claim) or (abstraction_basis in {"heldout-rule", "symbolic-rule"} and extrapolation)
        status = "pass" if ok else "fail"
        reason = None if ok else "rule-abstraction claim lacks heldout abstraction basis"
    return _gate(
        "CV-HG3",
        status=status,
        criterion="finite table evidence is separated from rule-abstraction authority",
        evidence_pointer="$.construct_validity_hardgates.evidence.finite_table",
        reason=reason,
        coverage_status=coverage_status or None,
        rule_abstraction_claim=rule_claim,
        finite_pair_accuracy=finite_accuracy,
    )


def _gate_cv_hg4(evidence: ConstructValidityEvidence) -> dict[str, Any]:
    ledger = _mapping(evidence.hand_feature_ledger)
    mode = str(ledger.get("mode", ledger.get("status", ""))).strip()
    features = tuple(str(item) for item in _list_cell(ledger.get("features", ())) if str(item))
    candidate_only = tuple(str(item) for item in _list_cell(ledger.get("candidate_only_features", ())) if str(item))
    shared = _bool_cell(ledger.get("shared_across_arms"), default=False)
    no_gate = mode in {"no-gate", "no-hand-features", "none"} and not features and not candidate_only
    shared_gate = mode in {"shared-gate", "shared-feature-ledger", "pass"} and shared and not candidate_only
    ok = bool(ledger) and (no_gate or shared_gate)
    return _gate(
        "CV-HG4",
        status="pass" if ok else "fail",
        criterion="hand features are absent or declared as shared across candidate and controls",
        evidence_pointer="$.construct_validity_hardgates.evidence.hand_feature_ledger",
        reason=None if ok else "candidate-only hand feature or missing shared/no-gate ledger",
        ledger_mode=mode or None,
        candidate_only_features=list(candidate_only),
    )


def _gate_cv_hg5(evidence: ConstructValidityEvidence) -> dict[str, Any]:
    metric = _mapping(evidence.metric_source)
    source_kind = str(metric.get("source_kind", metric.get("kind", ""))).strip()
    forbidden_sources = tuple(str(item) for item in _list_cell(metric.get("forbidden_sources", ())) if str(item))
    per_arm_constants = _bool_cell(metric.get("per_arm_constants"), default=False)
    label_derived = _bool_cell(metric.get("label_derived_metric_source"), default=False)
    metric_keys = _list_cell(metric.get("metric_keys", ()))
    forbidden_kinds = {"per-arm-constant", "per_arm_constant", "scripted-table", "scripted_metric_table", "label-leakage"}
    ok = (
        bool(metric)
        and bool(metric_keys)
        and source_kind not in forbidden_kinds
        and not forbidden_sources
        and not per_arm_constants
        and not label_derived
    )
    return _gate(
        "CV-HG5",
        status="pass" if ok else "fail",
        criterion="metric source is training/evaluation evidence rather than per-arm constants, labels, or scripted tables",
        evidence_pointer="$.construct_validity_hardgates.evidence.metric_source",
        reason=None if ok else "metric source purity evidence is missing or contaminated",
        source_kind=source_kind or None,
        forbidden_sources=list(forbidden_sources),
        per_arm_constants=per_arm_constants,
        label_derived_metric_source=label_derived,
    )


def evaluate_construct_validity(
    evidence: ConstructValidityEvidence | Mapping[str, Any] | None,
) -> ConstructValidityAudit:
    if evidence is None:
        typed = ConstructValidityEvidence(None, None, None, None, None, None, None)
    else:
        typed = ConstructValidityEvidence.from_payload(evidence)
    gates = {
        "CV-HG1": _gate_cv_hg1(typed),
        "CV-HG2": _gate_cv_hg2(typed),
        "CV-HG3": _gate_cv_hg3(typed),
        "CV-HG4": _gate_cv_hg4(typed),
        "CV-HG5": _gate_cv_hg5(typed),
    }
    failed = tuple(gate_id for gate_id in GATE_IDS if gates[gate_id]["status"] != "pass")
    status = "pass" if not failed else "fail"
    audit = ConstructValidityAudit(
        status=status,
        failed_gates=failed,
        gates=gates,
        claim_capsule_projection={
            "artifact": OWNER_MODULE,
            "pointer": OWNER_POINTER,
            "status": status,
            "failed_gates": list(failed),
            "owner_pointer": OWNER_POINTER,
        },
    )
    return audit


def construct_validity_projection(
    evidence: ConstructValidityEvidence | Mapping[str, Any],
    *,
    artifact: str,
    pointer: str = "$.construct_validity_hardgates",
) -> dict[str, Any]:
    typed = ConstructValidityEvidence.from_payload(evidence)
    audit = evaluate_construct_validity(evidence)
    payload = audit.as_payload(artifact=artifact, pointer=pointer)
    payload["evidence"] = typed.as_payload()
    return payload


__all__ = [
    "ARTIFACT_ID",
    "CLAIM_CAPSULE_PROJECTION_KEYS",
    "ConstructValidityAudit",
    "ConstructValidityEvidence",
    "GATE_IDS",
    "OWNER_MODULE",
    "OWNER_POINTER",
    "SCHEMA_ID",
    "construct_validity_projection",
    "evaluate_construct_validity",
]
