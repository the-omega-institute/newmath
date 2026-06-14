"""Pointer-only fair L1 decision for the bounded tiny-sequence evidence."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:fair-l1-decision"
ARTIFACT_ID = "bedc-quality-lab:fair-l1-decision"
PRODUCER = "scripts/run_fair_l1_decision.py"
OWNER_MODULE = "bedc_quality_lab/fair_l1_decision.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/fair-l1-decision.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/fair-l1-decision.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/fair-l1-decision.fingerprint.json"
GENERATED_AT = "2026-06-12T00:00:00+08:00"
LAB_ROOT = Path(__file__).resolve().parents[1]

DGT_L1_CONTROLS_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
DGT_BASE_UNDERTRAINING_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.json"
INPUT_ACCESSIBILITY_ARTIFACT = "reports/canonical/input-accessibility.json"

L1_PROJECTION_POINTER = f"{DGT_L1_CONTROLS_ARTIFACT}:$.l1_tiny_sequence_projection"
L1_STEP_LADDER_POINTER = f"{DGT_L1_CONTROLS_ARTIFACT}:$.l1_step_ladder"
L1_OOD_MECHANISM_POINTER = f"{DGT_L1_CONTROLS_ARTIFACT}:$.l1_ood_mechanism"
L1_CONSTRUCT_VALIDITY_POINTER = f"{DGT_L1_CONTROLS_ARTIFACT}:$.construct_validity_ledger"
BASE_AUDIT_POINTER = f"{DGT_BASE_UNDERTRAINING_ARTIFACT}:$.base_undertraining_audit"
INPUT_ACCESSIBILITY_POINTER = f"{INPUT_ACCESSIBILITY_ARTIFACT}:$"
LADDER_STATE_PROJECTION_POINTER = f"{CANONICAL_JSON_ARTIFACT}:$.ladder_state_projection"
INPUT_ABLATION_ARM_ID = "input_ablation_masked_tail"
INPUT_ABLATION_ROLE = "ablation"

DECISION_STATUSES = ("blocked", "bounded-negative", "scaling-evidence-eligible")
LADDER_STATES = ("l1-scaling-blocked", "l1-bounded-negative", "l1-scaling-evidence-eligible")
HARDGATE_IDS = tuple(f"FAIR-L1-HG{index}" for index in range(1, 8))
REQUIRED_COMPARISONS = (
    "equal-step",
    "equal-compute",
    "equal-loss-decrease",
    "equal-validation-loss",
)
NOT_CLAIMED = (
    "Bounded L1 tiny-sequence decision only.",
    "No L2 or higher scaling claim.",
    "No production deployment claim.",
    "No global model superiority claim.",
    "No LLM replacement claim.",
    "No OOD generalization claim.",
    "No architecture advantage claim.",
)


@dataclass(frozen=True)
class SourceCell:
    artifact: str
    pointer: str
    status: str
    sha256: str | None
    value: Any

    def as_ref(self) -> dict[str, Any]:
        payload = {
            "artifact": self.artifact,
            "pointer": self.pointer,
            "status": self.status,
        }
        if self.sha256 is not None:
            payload["sha256"] = self.sha256
        return payload


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _split_artifact_pointer(artifact_pointer: str) -> tuple[str, str]:
    if ":" not in artifact_pointer:
        raise ValueError(f"invalid artifact pointer: {artifact_pointer}")
    artifact, pointer = artifact_pointer.split(":", 1)
    if not artifact or not pointer:
        raise ValueError(f"invalid artifact pointer: {artifact_pointer}")
    return artifact, pointer


def _resolve_cell(root: Path, artifact_pointer: str) -> SourceCell:
    artifact, pointer = _split_artifact_pointer(artifact_pointer)
    path = root / artifact
    digest = _sha256(path)
    if digest is None:
        return SourceCell(artifact=artifact, pointer=pointer, status="missing", sha256=None, value=None)
    value = resolve_artifact_pointer(root, artifact_pointer)
    if value is None:
        return SourceCell(artifact=artifact, pointer=pointer, status="pointer-missing", sha256=digest, value=None)
    return SourceCell(artifact=artifact, pointer=pointer, status="resolved", sha256=digest, value=value)


def _dig(value: Any, path: Sequence[str], default: Any = None) -> Any:
    cursor = value
    for key in path:
        if not isinstance(cursor, Mapping) or key not in cursor:
            return default
        cursor = cursor[key]
    return cursor


def _status_bool(status: Any, expected: str = "pass") -> bool:
    return isinstance(status, str) and status == expected


def _input_accessibility_row_pointer(row: Mapping[str, Any]) -> str:
    return f"{INPUT_ACCESSIBILITY_ARTIFACT}#row_id={row['row_id']}"


def _baseline_input_accessibility(input_accessibility: Any) -> dict[str, Any]:
    if not isinstance(input_accessibility, Mapping):
        return {"status": "missing", "failures": ["input-accessibility-owner-missing"]}
    rows = input_accessibility.get("rows")
    if not isinstance(rows, list):
        return {"status": "missing", "failures": ["input-accessibility-owner-rows-missing"]}
    matches = [
        row
        for row in rows
        if isinstance(row, Mapping)
        and row.get("experiment") == "dgt_l1_tiny_sequence"
        and row.get("split") == "in_distribution"
        and row.get("arm") == INPUT_ABLATION_ARM_ID
        and row.get("role") == INPUT_ABLATION_ROLE
    ]
    if len(matches) != 1:
        return {
            "status": "fail",
            "failures": ["baseline-input-accessibility-row-not-unique"],
            "row_count": len(matches),
        }
    row = matches[0]
    pointer = _input_accessibility_row_pointer(row)
    consumers = input_accessibility.get("consumer_pointers")
    information_refs = consumers.get("information_starved_arms_ref") if isinstance(consumers, Mapping) else None
    extraction_pass = (
        row.get("feature_extraction", {}).get("status") == "pass"
        and row.get("label_extraction", {}).get("status") == "pass"
    )
    failures: list[str] = []
    if not extraction_pass:
        failures.append("baseline-input-accessibility-extraction-failed")
    pointer_alignment = isinstance(information_refs, list) and ((pointer in information_refs) == bool(row.get("information_starved")))
    if not pointer_alignment:
        failures.append("baseline-input-accessibility-consumer-pointer-mismatch")
    return {
        "status": "pass" if not failures else "fail",
        "row_id": row.get("row_id"),
        "row_pointer": pointer,
        "visible_variables": list(row.get("visible_variables", [])),
        "required_variables": list(row.get("required_variables", [])),
        "missing_variables": list(row.get("missing_variables", [])),
        "information_starved": bool(row.get("information_starved")),
        "coverage_status": row.get("coverage_status"),
        "supports_architecture_claim": row.get("supports_architecture_claim"),
        "feature_extraction_status": row.get("feature_extraction", {}).get("status"),
        "label_extraction_status": row.get("label_extraction", {}).get("status"),
        "consumer_pointer_aligned": pointer_alignment,
        "failures": failures,
    }


def _comparison_rows(base_audit: Any) -> list[dict[str, Any]]:
    audit_rows = _dig(base_audit, ("comparison_rows",), [])
    rows: list[dict[str, Any]] = []
    if isinstance(audit_rows, list):
        for index, row in enumerate(audit_rows):
            if not isinstance(row, Mapping):
                continue
            rows.append(
                {
                    "comparison_id": str(row.get("comparison_id", "")).replace("_", "-"),
                    "status": row.get("status", "missing"),
                    "source_pointer": row.get("source_pointer"),
                    "owner_row_pointer": f"{BASE_AUDIT_POINTER}.comparison_rows[{index}]",
                    "match_axis": row.get("match_axis"),
                    "decision": row.get("decision"),
                }
            )
    rows_by_id = {str(row.get("comparison_id")): row for row in rows}
    if "equal-step" not in rows_by_id:
        rows.append(
            {
                "comparison_id": "equal-step",
                "status": "missing",
                "source_pointer": BASE_AUDIT_POINTER,
                "owner_row_pointer": BASE_AUDIT_POINTER,
                "match_axis": "training_steps",
                "decision": "required-evidence-missing",
            }
        )
    if "equal-compute" not in rows_by_id:
        rows.append(
            {
                "comparison_id": "equal-compute",
                "status": "missing",
                "source_pointer": BASE_AUDIT_POINTER,
                "owner_row_pointer": BASE_AUDIT_POINTER,
                "match_axis": "compute_units",
                "decision": "required-evidence-missing",
            }
        )
    if "equal-loss-decrease" not in rows_by_id:
        rows.append(
            {
                "comparison_id": "equal-loss-decrease",
                "status": "missing",
                "source_pointer": BASE_AUDIT_POINTER,
                "owner_row_pointer": BASE_AUDIT_POINTER,
                "match_axis": "loss_decrease",
                "decision": "required-evidence-missing",
            }
        )
    if "equal-validation-loss" not in rows_by_id:
        rows.append(
            {
                "comparison_id": "equal-validation-loss",
                "status": "missing",
                "source_pointer": BASE_AUDIT_POINTER,
                "owner_row_pointer": BASE_AUDIT_POINTER,
                "match_axis": "validation_loss",
                "decision": "required-evidence-missing",
            }
        )
    ordered: list[dict[str, Any]] = []
    by_id = {str(row["comparison_id"]): row for row in rows}
    for comparison_id in REQUIRED_COMPARISONS:
        ordered.append(dict(by_id[comparison_id]))
    return ordered


def _hardgate_row(gate_id: str, passed: bool, criterion: str, source_pointer: str, reason: str | None = None) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "pass" if passed else "fail",
        "criterion": criterion,
        "source_pointer": source_pointer,
        "fail_closed_reason": None if passed else reason or criterion,
    }


def _fair_hardgates(
    *,
    source_cells: Mapping[str, SourceCell],
    comparison_rows: Sequence[Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    l1_projection = source_cells["l1_projection"].value
    l1_ladder = source_cells["l1_step_ladder"].value
    l1_ood = source_cells["l1_ood_mechanism"].value
    l1_construct = source_cells["l1_construct_validity"].value
    base_audit = source_cells["base_audit"].value
    input_accessibility = source_cells["input_accessibility"].value

    resolved_inputs = all(cell.status == "resolved" for cell in source_cells.values())
    comparison_ok = all(row.get("status") == "resolved" for row in comparison_rows)
    baseline_access = _baseline_input_accessibility(input_accessibility)
    construct_ok = (
        _status_bool(_dig(l1_construct, ("status",)))
        and _dig(base_audit, ("construct_validity", "status")) != "construct-boundary"
        and baseline_access.get("status") == "pass"
        and baseline_access.get("information_starved") is False
        and baseline_access.get("missing_variables") == []
    )
    review_pass = _status_bool(_dig(l1_projection, ("status",))) and _status_bool(_dig(l1_projection, ("review_status",)))
    ladder_ok = _status_bool(_dig(l1_ladder, ("status",))) and _dig(l1_ladder, ("verdict",)) == "information-starved-catches-up"
    ood_ok = _dig(l1_projection, ("ood_generalization_claim",)) != "not-claimed" and _dig(l1_ood, ("verdict",)) == "partial-rule"
    base_not_starved = _dig(base_audit, ("construct_validity", "baseline_input_order")) == _dig(
        base_audit,
        ("construct_validity", "label_dependency_order"),
    ) and baseline_access.get("information_starved") is False
    gates = [
        _hardgate_row(
            "FAIR-L1-HG1",
            resolved_inputs,
            "required owner pointers resolve before any L1 decision is emitted",
            "$.source_artifacts",
            "one or more owner pointers are missing",
        ),
        _hardgate_row(
            "FAIR-L1-HG2",
            comparison_ok,
            "equal-step, equal-compute, equal-loss-decrease, and equal-validation-loss rows are resolved",
            "$.fair_alignment.comparison_rows",
            "one or more fair alignment rows are missing",
        ),
        _hardgate_row(
            "FAIR-L1-HG3",
            construct_ok,
            "baseline arm has enough task information for a fair architecture comparison",
            BASE_AUDIT_POINTER,
            "baseline arm is information-starved or input-accessibility rows mark missing variables",
        ),
        _hardgate_row(
            "FAIR-L1-HG4",
            review_pass,
            "bounded L1 controls pass their owner-local review",
            L1_PROJECTION_POINTER,
            "L1 controls projection is not pass",
        ),
        _hardgate_row(
            "FAIR-L1-HG5",
            ladder_ok,
            "step-ladder verdict supplies positive fair scaling evidence",
            L1_STEP_LADDER_POINTER,
            "step-ladder evidence does not support fair scaling promotion",
        ),
        _hardgate_row(
            "FAIR-L1-HG6",
            ood_ok,
            "OOD mechanism evidence is above boundary-only status",
            L1_OOD_MECHANISM_POINTER,
            "OOD mechanism remains diagnostic or not claimed",
        ),
        _hardgate_row(
            "FAIR-L1-HG7",
            base_not_starved,
            "baseline can in principle express the target dependency",
            BASE_AUDIT_POINTER,
            "baseline Bayes limit is chance under the owner construct-validity proof",
        ),
    ]
    return {row["gate_id"]: row for row in gates}


def _derive_decision(gates: Mapping[str, Mapping[str, Any]]) -> tuple[str, str]:
    failed = [gate_id for gate_id in HARDGATE_IDS if gates[gate_id]["status"] != "pass"]
    if not failed:
        return "scaling-evidence-eligible", "l1-scaling-evidence-eligible"
    if "FAIR-L1-HG1" in failed:
        return "blocked", "l1-scaling-blocked"
    return "bounded-negative", "l1-bounded-negative"


def _decision_payload(
    *,
    gates: Mapping[str, Mapping[str, Any]],
    comparison_rows: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    status, ladder_state = _derive_decision(gates)
    failed = [gate_id for gate_id in HARDGATE_IDS if gates[gate_id]["status"] != "pass"]
    boundary_rows = [
        {
            "gate_id": gate_id,
            "status": "blocked" if gate_id == "FAIR-L1-HG1" else "bounded-negative",
            "reason": str(gates[gate_id].get("fail_closed_reason") or "fair L1 gate failed"),
            "source_pointer": gates[gate_id]["source_pointer"],
        }
        for gate_id in failed
    ]
    return {
        "status": status,
        "allowed_statuses": list(DECISION_STATUSES),
        "claim_id": "claim:fair-l1-decision",
        "failed_gate": failed[0] if failed else None,
        "hardgate_status": "pass" if not failed else "fail",
        "hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.hardgates",
        "comparison_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.fair_alignment.comparison_rows",
        "boundary_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.boundary_ledger",
        "ladder_state": ladder_state,
        "claim_capsule": {
            "schema_id": "bedc.quality.claim_capsule",
            "status": "pointer-only",
            "claim_id": "claim:fair-l1-decision",
            "evidence_pointers": [
                L1_PROJECTION_POINTER,
                L1_STEP_LADDER_POINTER,
                L1_OOD_MECHANISM_POINTER,
                BASE_AUDIT_POINTER,
                INPUT_ACCESSIBILITY_POINTER,
                f"{CANONICAL_JSON_ARTIFACT}:$.decision.status",
                f"{CANONICAL_JSON_ARTIFACT}:$.ladder_state_projection.state",
            ],
            "projection_pointers": [
                f"{CANONICAL_JSON_ARTIFACT}:$.decision",
                LADDER_STATE_PROJECTION_POINTER,
            ],
            "not_claimed": list(NOT_CLAIMED),
        },
        "mechanical_rule": {
            "blocked": "any required owner pointer is missing",
            "bounded-negative": "owner pointers resolve but any fair comparison, construct-validity, step-ladder, or OOD gate fails",
            "scaling-evidence-eligible": "all fair L1 hardgates pass",
        },
        "comparison_count": len(comparison_rows),
    }


def build_payload(*, root: Path | None = None, generated_at: str = GENERATED_AT) -> dict[str, Any]:
    active_root = root or LAB_ROOT
    source_cells = {
        "l1_projection": _resolve_cell(active_root, L1_PROJECTION_POINTER),
        "l1_step_ladder": _resolve_cell(active_root, L1_STEP_LADDER_POINTER),
        "l1_ood_mechanism": _resolve_cell(active_root, L1_OOD_MECHANISM_POINTER),
        "l1_construct_validity": _resolve_cell(active_root, L1_CONSTRUCT_VALIDITY_POINTER),
        "base_audit": _resolve_cell(active_root, BASE_AUDIT_POINTER),
        "input_accessibility": _resolve_cell(active_root, INPUT_ACCESSIBILITY_POINTER),
    }
    comparison_rows = _comparison_rows(source_cells["base_audit"].value)
    gates = _fair_hardgates(source_cells=source_cells, comparison_rows=comparison_rows)
    decision = _decision_payload(gates=gates, comparison_rows=comparison_rows)
    status = decision["status"]
    boundary = [
        {
            "gate_id": gate_id,
            "status": "blocked" if gate_id == "FAIR-L1-HG1" else "bounded-negative",
            "reason": str(row.get("fail_closed_reason") or "fair L1 gate failed"),
            "source_pointer": row["source_pointer"],
        }
        for gate_id, row in gates.items()
        if row["status"] != "pass"
    ]
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "owner_module": OWNER_MODULE,
        "source_artifacts": {key: cell.as_ref() for key, cell in source_cells.items()},
        "fair_alignment": {
            "comparison_ids": list(REQUIRED_COMPARISONS),
            "comparison_rows": list(comparison_rows),
            "source_pointer": BASE_AUDIT_POINTER,
        },
        "construct_validity_projection": {
            "l1_construct_validity_pointer": L1_CONSTRUCT_VALIDITY_POINTER,
            "base_construct_validity_pointer": f"{BASE_AUDIT_POINTER}.construct_validity",
            "input_accessibility_pointer": INPUT_ACCESSIBILITY_POINTER,
            "status": "pass" if gates["FAIR-L1-HG3"]["status"] == "pass" else "bounded-negative",
        },
        "ood_projection": {
            "l1_projection_pointer": L1_PROJECTION_POINTER,
            "mechanism_pointer": L1_OOD_MECHANISM_POINTER,
            "status": "pass" if gates["FAIR-L1-HG6"]["status"] == "pass" else "bounded-negative",
        },
        "hardgates": gates,
        "decision": decision,
        "ladder_state_projection": {
            "state": decision["ladder_state"],
            "allowed_states": list(LADDER_STATES),
            "decision_status": status,
            "decision_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.decision.status",
            "hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.hardgates",
            "boundary_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.boundary_ledger",
            "not_claimed": list(NOT_CLAIMED),
        },
        "boundary_ledger": boundary,
        "not_claimed": list(NOT_CLAIMED),
    }
    validate_payload(payload, root=active_root)
    return payload


def validate_payload(payload: Mapping[str, Any], *, root: Path | None = None) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "owner_module",
        "source_artifacts",
        "fair_alignment",
        "construct_validity_projection",
        "ood_projection",
        "hardgates",
        "decision",
        "ladder_state_projection",
        "boundary_ledger",
        "not_claimed",
    }
    if set(payload) != required:
        raise ValueError("fair L1 decision fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("fair L1 decision identity mismatch")
    gates = payload["hardgates"]
    if not isinstance(gates, Mapping) or set(gates) != set(HARDGATE_IDS):
        raise ValueError("fair L1 hardgate ids mismatch")
    for gate_id in HARDGATE_IDS:
        row = gates[gate_id]
        if not isinstance(row, Mapping) or row.get("gate_id") != gate_id or row.get("status") not in {"pass", "fail"}:
            raise ValueError(f"fair L1 hardgate row invalid: {gate_id}")
    comparison_rows = _dig(payload, ("fair_alignment", "comparison_rows"), [])
    if not isinstance(comparison_rows, list) or [row.get("comparison_id") for row in comparison_rows] != list(REQUIRED_COMPARISONS):
        raise ValueError("fair L1 comparison rows mismatch")
    expected_status, expected_state = _derive_decision(gates)
    decision = payload["decision"]
    if decision.get("status") not in DECISION_STATUSES or decision.get("allowed_statuses") != list(DECISION_STATUSES):
        raise ValueError("fair L1 decision status domain mismatch")
    if decision.get("status") != expected_status or decision.get("ladder_state") != expected_state:
        raise ValueError("fair L1 decision table mismatch")
    capsule = decision.get("claim_capsule")
    if not isinstance(capsule, Mapping) or capsule.get("status") != "pointer-only":
        raise ValueError("fair L1 ClaimCapsule must be pointer-only")
    capsule_text = json.dumps(capsule, sort_keys=True)
    for forbidden in ("comparison_rows", "construct_validity_projection", "ood_projection", "fair_alignment"):
        if forbidden in capsule_text:
            raise ValueError("fair L1 ClaimCapsule copied owner prose or evidence body")
    ladder = payload["ladder_state_projection"]
    if ladder.get("state") not in LADDER_STATES or ladder.get("allowed_states") != list(LADDER_STATES):
        raise ValueError("fair L1 ladder state domain mismatch")
    if ladder.get("state") != expected_state or ladder.get("decision_status") != expected_status:
        raise ValueError("fair L1 ladder state projection mismatch")
    expected_boundary = [
        {
            "gate_id": gate_id,
            "status": "blocked" if gate_id == "FAIR-L1-HG1" else "bounded-negative",
            "reason": str(gates[gate_id].get("fail_closed_reason") or "fair L1 gate failed"),
            "source_pointer": gates[gate_id]["source_pointer"],
        }
        for gate_id in HARDGATE_IDS
        if gates[gate_id]["status"] != "pass"
    ]
    if payload["boundary_ledger"] != expected_boundary:
        raise ValueError("fair L1 boundary ledger mismatch")
    text = json.dumps(payload, sort_keys=True)
    for token in ("unblocked", "scoped-boundary", "base_transformer" + "_l1"):
        if token in text:
            raise ValueError(f"fair L1 payload contains forbidden token: {token}")
    active_root = root or LAB_ROOT
    for key, row in payload["source_artifacts"].items():
        if not isinstance(row, Mapping) or "artifact" not in row or "pointer" not in row:
            raise ValueError(f"fair L1 source artifact invalid: {key}")
        if row.get("status") == "resolved":
            pointer = f"{row['artifact']}:{row['pointer']}"
            if resolve_artifact_pointer(active_root, pointer) is None:
                raise ValueError(f"fair L1 source pointer does not resolve: {pointer}")


def render_markdown(payload: Mapping[str, Any], *, root: Path | None = None) -> str:
    validate_payload(payload, root=root or LAB_ROOT)
    lines = [
        "# Fair L1 Decision",
        "",
        f"- Status: `{payload['decision']['status']}`",
        f"- Ladder state: `{payload['ladder_state_projection']['state']}`",
        f"- Failed gate: `{payload['decision']['failed_gate']}`",
        "",
        "## Hardgates",
        "",
    ]
    for gate_id in HARDGATE_IDS:
        row = payload["hardgates"][gate_id]
        lines.append(f"- `{gate_id}`: `{row['status']}` - {row['criterion']}")
    lines.extend(["", "## Fair Alignment", ""])
    for row in payload["fair_alignment"]["comparison_rows"]:
        lines.append(f"- `{row['comparison_id']}`: `{row['status']}` - `{row['decision']}`")
    lines.extend(["", "## Boundary Ledger", ""])
    if payload["boundary_ledger"]:
        for row in payload["boundary_ledger"]:
            lines.append(f"- `{row['gate_id']}`: `{row['status']}` - {row['reason']}")
    else:
        lines.append("- No boundary rows.")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    del generated_at
    validate_payload(payload, root=root)
    _write_json(root / CANONICAL_JSON_ARTIFACT, payload)
    _write_text(root / CANONICAL_MARKDOWN_ARTIFACT, render_markdown(payload, root=root))


__all__ = [
    "ARTIFACT_ID",
    "CANONICAL_FINGERPRINT_ARTIFACT",
    "CANONICAL_JSON_ARTIFACT",
    "CANONICAL_MARKDOWN_ARTIFACT",
    "DECISION_STATUSES",
    "GENERATED_AT",
    "HARDGATE_IDS",
    "LADDER_STATE_PROJECTION_POINTER",
    "LADDER_STATES",
    "PRODUCER",
    "SCHEMA_ID",
    "build_payload",
    "render_markdown",
    "validate_payload",
    "write_artifacts",
]
