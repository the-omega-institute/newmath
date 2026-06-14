"""Canonical owner for scaling-ladder opening decisions."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
from collections.abc import Mapping, Sequence
from typing import Any

from bedc_quality_lab.construct_validity import (
    GATE_IDS as CONSTRUCT_VALIDITY_GATE_IDS,
    OWNER_POINTER as CONSTRUCT_VALIDITY_OWNER_POINTER,
    SCHEMA_ID as CONSTRUCT_VALIDITY_SCHEMA_ID,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer, split_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:scaling-ladder"
ARTIFACT_ID = "bedc-quality-lab:scaling-ladder"
PRODUCER = "scripts/run_scaling_ladder.py"
LADDER_ELIGIBILITY_STATUS = "scaling-evidence-eligible"
JSON_ARTIFACT = "reports/canonical/scaling-ladder.json"
MARKDOWN_ARTIFACT = "reports/canonical/scaling-ladder.md"
FINGERPRINT_ARTIFACT = "reports/canonical/scaling-ladder.fingerprint.json"
INDEX_ARTIFACT = "reports/canonical/index.json"
DGT_JSON_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
DGT_L0_CONTROLS_JSON_ARTIFACT = "reports/canonical/dgt-l0-controls.json"
DGT_L1_CONTROLS_JSON_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
EVIDENCE_PROVENANCE_POINTER = f"{INDEX_ARTIFACT}:$.evidence_provenance"
CONSTRUCT_VALIDITY_POINTER = f"{DGT_L1_CONTROLS_JSON_ARTIFACT}:$.fair_l1_construction.construct_validity"
DGT_SCALING_LADDER_POINTER = f"{DGT_JSON_ARTIFACT}:$.scaling_ladder"
ALLOWED_STATES = ("open", "closed", "boundary")
ALLOWED_REASONS = (
    "eligible",
    "missing-pointer",
    "unresolved-pointer",
    "non-measured-evidence",
    "construct-validity-failed",
    "split-not-winnable",
    "ci-low-separation-failed",
    "owner-negative",
    "projection-only",
    "stale-or-injected",
)
NOT_CLAIMED = (
    "Scaling-ladder decisions are bounded canonical owner rows.",
    "No non-owner artifact is an opening authority.",
    "No production, global superiority, or natural-language capability claim is made.",
    "Missing upstream owner contracts fail closed rather than inheriting adjacent level decisions.",
)


@dataclass(frozen=True)
class LadderOpeningRef:
    level_id: str
    level_owner_artifact: str
    level_owner_pointer: str
    evidence_provenance_pointer: str
    construct_validity_pointer: str
    decision_pointer: str
    split_winnability_pointer: str
    separation_pointer: str
    expected_evidence_class: str


@dataclass(frozen=True)
class LadderOpeningDecision:
    level_id: str
    state: str
    reason: str
    owner_decision_pointer: str
    evidence_provenance_pointer: str
    construct_validity_pointer: str
    split_winnability_pointer: str
    separation_pointer: str
    source_report_pointer: str
    boundary_ledger_pointer: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def default_ladder_refs() -> tuple[LadderOpeningRef, ...]:
    return (
        LadderOpeningRef(
            level_id="L0_toy",
            level_owner_artifact=DGT_L0_CONTROLS_JSON_ARTIFACT,
            level_owner_pointer=f"{DGT_L0_CONTROLS_JSON_ARTIFACT}:$.l0_toy_projection",
            evidence_provenance_pointer=EVIDENCE_PROVENANCE_POINTER,
            construct_validity_pointer=CONSTRUCT_VALIDITY_POINTER,
            decision_pointer=f"{DGT_L0_CONTROLS_JSON_ARTIFACT}:$.l0_toy_projection.owner_decision",
            split_winnability_pointer=f"{DGT_L0_CONTROLS_JSON_ARTIFACT}:$.l0_toy_projection.split_winnability",
            separation_pointer=f"{DGT_L0_CONTROLS_JSON_ARTIFACT}:$.l0_toy_projection.separation",
            expected_evidence_class="empirical_training_clean",
        ),
        LadderOpeningRef(
            level_id="L1_tiny_sequence",
            level_owner_artifact=DGT_L1_CONTROLS_JSON_ARTIFACT,
            level_owner_pointer=f"{DGT_L1_CONTROLS_JSON_ARTIFACT}:$.l1_tiny_sequence_projection",
            evidence_provenance_pointer=EVIDENCE_PROVENANCE_POINTER,
            construct_validity_pointer=CONSTRUCT_VALIDITY_POINTER,
            decision_pointer=f"{DGT_L1_CONTROLS_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.fair_decision",
            split_winnability_pointer=f"{DGT_L1_CONTROLS_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.split_winnability",
            separation_pointer=f"{DGT_L1_CONTROLS_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.separation",
            expected_evidence_class="empirical_training_clean",
        ),
    )


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _resolve(root: Path, pointer: str) -> tuple[str, Any]:
    split = split_artifact_pointer(pointer)
    if split is None:
        return "missing-pointer", None
    artifact, _local = split
    if not (root / artifact).exists():
        return "missing-pointer", None
    value = resolve_artifact_pointer(root, pointer)
    if value is None:
        return "unresolved-pointer", None
    return "resolved", value


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _reason_for_provenance(ref: LadderOpeningRef, value: Any) -> str | None:
    provenance = _mapping(value)
    level_records = provenance.get("levels")
    if isinstance(level_records, Mapping):
        provenance = _mapping(level_records.get(ref.level_id))
    elif isinstance(level_records, Sequence) and not isinstance(level_records, (str, bytes, bytearray)):
        provenance = next(
            (
                _mapping(row)
                for row in level_records
                if isinstance(row, Mapping) and row.get("level_id") == ref.level_id
            ),
            {},
        )
    if not provenance:
        return "unresolved-pointer"
    if provenance.get("source_kind") in {"projection-only", "projection_only"} or provenance.get("projection_only") is True:
        return "projection-only"
    if provenance.get("source_kind") in {"arm-branch", "arm_branch", "declared-constant", "declared_constant"}:
        return "non-measured-evidence"
    if provenance.get("evidence_type") != ref.expected_evidence_class:
        return "non-measured-evidence"
    if provenance.get("owner_backed_measured_training") is not True:
        return "non-measured-evidence"
    if provenance.get("allowed_for_empirical_claim") is not True:
        return "non-measured-evidence"
    return None


def _construct_passes(value: Any) -> bool:
    construct = _mapping(value)
    if (
        construct.get("status") == "construct-valid"
        and construct.get("source_pointer") == f"{DGT_L1_CONTROLS_JSON_ARTIFACT}:$.construct_validity_ledger"
        and construct.get("folded_into_pointer") == CONSTRUCT_VALIDITY_POINTER
    ):
        return True
    if construct.get("schema_id") != CONSTRUCT_VALIDITY_SCHEMA_ID:
        return False
    if construct.get("owner_pointer") != CONSTRUCT_VALIDITY_OWNER_POINTER:
        return False
    if construct.get("status") != "pass":
        return False
    failed_gates = construct.get("failed_gates")
    if failed_gates != []:
        return False
    gates = construct.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(CONSTRUCT_VALIDITY_GATE_IDS):
        return False
    for gate_id in CONSTRUCT_VALIDITY_GATE_IDS:
        gate = _mapping(gates.get(gate_id))
        if gate.get("gate_id") != gate_id or gate.get("status") != "pass":
            return False
    return True


def _decision_passes(value: Any) -> bool:
    decision = _mapping(value)
    return decision.get("status") == LADDER_ELIGIBILITY_STATUS


def _split_winnable(value: Any) -> bool:
    split = _mapping(value)
    if split.get("winnable") is True:
        return True
    if split.get("status") in {"pass", "winnable"}:
        return True
    return False


def _separation_passes(value: Any) -> bool:
    separation = _mapping(value)
    ci_low = separation.get("ci_low")
    if ci_low is None:
        ci_low = separation.get("ci95_low")
    if ci_low is None:
        ci_low = separation.get("ci_low_separation")
    return isinstance(ci_low, (int, float)) and not isinstance(ci_low, bool) and float(ci_low) > 0.0


def _old_injected_ladder(root: Path, ref: LadderOpeningRef) -> Mapping[str, Any] | None:
    projection = resolve_artifact_pointer(root, DGT_SCALING_LADDER_POINTER)
    if not isinstance(projection, Mapping):
        return None
    opened = projection.get("opened_levels")
    if isinstance(opened, Sequence) and not isinstance(opened, (str, bytes, bytearray)) and ref.level_id in opened:
        return projection
    levels = projection.get("levels")
    if isinstance(levels, Sequence) and not isinstance(levels, (str, bytes, bytearray)):
        for row in levels:
            if not isinstance(row, Mapping) or row.get("level_id") != ref.level_id:
                continue
            capsule = row.get("claim_capsule")
            if isinstance(capsule, Mapping) and capsule.get("level_state") in {"open", "ready"}:
                return capsule
    return None


def evaluate_ladder_opening(
    ref: LadderOpeningRef,
    context: Mapping[str, Any],
) -> LadderOpeningDecision:
    root = Path(context.get("root", "."))
    boundary_pointer = f"{JSON_ARTIFACT}:$.boundary_ledger"
    if _old_injected_ladder(root, ref) is not None:
        return LadderOpeningDecision(
            level_id=ref.level_id,
            state="boundary",
            reason="stale-or-injected",
            owner_decision_pointer=ref.decision_pointer,
            evidence_provenance_pointer=ref.evidence_provenance_pointer,
            construct_validity_pointer=ref.construct_validity_pointer,
            split_winnability_pointer=ref.split_winnability_pointer,
            separation_pointer=ref.separation_pointer,
            source_report_pointer=ref.level_owner_pointer,
            boundary_ledger_pointer=boundary_pointer,
        )
    pointer_by_name = {
        "evidence": ref.evidence_provenance_pointer,
        "construct": ref.construct_validity_pointer,
        "decision": ref.decision_pointer,
        "split": ref.split_winnability_pointer,
        "separation": ref.separation_pointer,
        "source": ref.level_owner_pointer,
    }
    values: dict[str, Any] = {}
    status_by_name: dict[str, str] = {}
    for name, pointer in pointer_by_name.items():
        status, value = _resolve(root, pointer)
        status_by_name[name] = status
        if status == "resolved":
            values[name] = value
    for name in ("evidence", "construct", "decision", "split", "separation"):
        status = status_by_name[name]
        if status != "resolved":
            reason = status
            state = "closed"
            return LadderOpeningDecision(
                level_id=ref.level_id,
                state=state,
                reason=reason,
                owner_decision_pointer=ref.decision_pointer,
                evidence_provenance_pointer=ref.evidence_provenance_pointer,
                construct_validity_pointer=ref.construct_validity_pointer,
                split_winnability_pointer=ref.split_winnability_pointer,
                separation_pointer=ref.separation_pointer,
                source_report_pointer=ref.level_owner_pointer,
                boundary_ledger_pointer=boundary_pointer,
            )
    provenance_reason = _reason_for_provenance(ref, values["evidence"])
    if provenance_reason is not None:
        state, reason = "closed", provenance_reason
    elif not _construct_passes(values["construct"]):
        state, reason = "closed", "construct-validity-failed"
    elif not _decision_passes(values["decision"]):
        state, reason = "closed", "owner-negative"
    elif not _split_winnable(values["split"]):
        state, reason = "closed", "split-not-winnable"
    elif not _separation_passes(values["separation"]):
        state, reason = "closed", "ci-low-separation-failed"
    else:
        state, reason = "open", "eligible"
    return LadderOpeningDecision(
        level_id=ref.level_id,
        state=state,
        reason=reason,
        owner_decision_pointer=ref.decision_pointer,
        evidence_provenance_pointer=ref.evidence_provenance_pointer,
        construct_validity_pointer=ref.construct_validity_pointer,
        split_winnability_pointer=ref.split_winnability_pointer,
        separation_pointer=ref.separation_pointer,
        source_report_pointer=ref.level_owner_pointer,
        boundary_ledger_pointer=boundary_pointer,
    )


def _boundary_row(row: Mapping[str, Any], *, recorded_at: str) -> dict[str, Any]:
    failed_pointer_by_reason = {
        "missing-pointer": row["owner_decision_pointer"],
        "unresolved-pointer": row["owner_decision_pointer"],
        "non-measured-evidence": row["evidence_provenance_pointer"],
        "construct-validity-failed": row["construct_validity_pointer"],
        "split-not-winnable": row["split_winnability_pointer"],
        "ci-low-separation-failed": row["separation_pointer"],
        "owner-negative": row["owner_decision_pointer"],
        "projection-only": row["evidence_provenance_pointer"],
        "stale-or-injected": DGT_SCALING_LADDER_POINTER,
    }
    failed_pointer = failed_pointer_by_reason.get(row["reason"], row["source_report_pointer"])
    return {
        "level_id": row["level_id"],
        "prior_state": "open",
        "new_state": row["state"],
        "reason": row["reason"],
        "failed_contract_pointer": failed_pointer,
        "owner_pointer": f"{JSON_ARTIFACT}:$.levels",
        "recorded_at": recorded_at,
    }


def _resolved_owner_value(root: Path, pointer: str | None) -> Any:
    if pointer is None:
        return None
    return resolve_artifact_pointer(root, pointer)


_CONTRACTS_BY_FIELD = {
    "owner_decision_pointer": "owner_decision",
    "evidence_provenance_pointer": "evidence_provenance",
    "construct_validity_pointer": "construct_validity",
    "split_winnability_pointer": "split_winnability",
    "separation_pointer": "separation",
    "source_report_pointer": "source_report",
}


def _contract_pointer(index: int, name: str) -> str:
    return f"{JSON_ARTIFACT}:$.levels[{index}].owner_contracts.{name}"


def _required_pointers(ref: LadderOpeningRef) -> dict[str, str]:
    return {
        "owner_decision": ref.decision_pointer,
        "evidence_provenance": ref.evidence_provenance_pointer,
        "construct_validity": ref.construct_validity_pointer,
        "split_winnability": ref.split_winnability_pointer,
        "separation": ref.separation_pointer,
        "source_report": ref.level_owner_pointer,
    }


def _attach_owner_contracts(
    row: Mapping[str, Any],
    *,
    ref: LadderOpeningRef,
    index: int,
    root: Path,
) -> dict[str, Any]:
    next_row = dict(row)
    contracts: dict[str, dict[str, str]] = {}
    required_by_name = _required_pointers(ref)
    field_by_contract = {contract: field for field, contract in _CONTRACTS_BY_FIELD.items()}
    for name, required_pointer in required_by_name.items():
        status, _value = _resolve(root, required_pointer)
        contracts[name] = {
            "required_pointer": required_pointer,
            "resolution_status": status,
        }
        field = field_by_contract[name]
        next_row[field] = required_pointer if status == "resolved" else _contract_pointer(index, name)
    next_row["owner_contracts"] = contracts
    return next_row


def _resolve_payload_or_artifact(root: Path, payload: Mapping[str, Any], pointer: str | None) -> Any:
    if pointer is None:
        return None
    split = split_artifact_pointer(pointer)
    if split is None:
        return None
    artifact, local_pointer = split
    if artifact == JSON_ARTIFACT:
        return pointer_value(payload, local_pointer)
    return resolve_artifact_pointer(root, pointer)


def _required_pointer(row: Mapping[str, Any], name: str) -> str | None:
    contracts = row.get("owner_contracts")
    if not isinstance(contracts, Mapping):
        return None
    contract = contracts.get(name)
    if not isinstance(contract, Mapping):
        return None
    pointer = contract.get("required_pointer")
    return pointer if isinstance(pointer, str) else None


def _gate_statuses(
    root: Path,
    decisions: Sequence[Mapping[str, Any]],
    *,
    refs: Sequence[LadderOpeningRef] | None = None,
) -> dict[str, str]:
    evidence_fail = False
    construct_fail = False
    decision_fail = False
    split_separation_fail = False
    ref_by_level = {ref.level_id: ref for ref in (default_ladder_refs() if refs is None else refs)}
    for row in decisions:
        ref = ref_by_level.get(str(row.get("level_id")))
        evidence_value = _resolved_owner_value(root, _required_pointer(row, "evidence_provenance"))
        construct_value = _resolved_owner_value(root, _required_pointer(row, "construct_validity"))
        decision_value = _resolved_owner_value(root, _required_pointer(row, "owner_decision"))
        split_value = _resolved_owner_value(root, _required_pointer(row, "split_winnability"))
        separation_value = _resolved_owner_value(root, _required_pointer(row, "separation"))
        if ref is None or evidence_value is None or _reason_for_provenance(ref, evidence_value) is not None:
            evidence_fail = True
        if construct_value is None or not _construct_passes(construct_value):
            construct_fail = True
        if decision_value is None or not _decision_passes(decision_value):
            decision_fail = True
        if (
            split_value is None
            or separation_value is None
            or not _split_winnable(split_value)
            or not _separation_passes(separation_value)
        ):
            split_separation_fail = True
    return {
        "SL-HG1-evidence-provenance": "fail" if evidence_fail else "pass",
        "SL-HG2-construct-validity": "fail" if construct_fail else "pass",
        "SL-HG3-owner-decision": "fail" if decision_fail else "pass",
        "SL-HG4-split-separation": "fail" if split_separation_fail else "pass",
    }


def _expected_level_rows(
    root: Path,
    refs: Sequence[LadderOpeningRef] | None = None,
) -> list[dict[str, Any]]:
    ref_rows = list(default_ladder_refs() if refs is None else refs)
    return [
        _attach_owner_contracts(
            evaluate_ladder_opening(ref, {"root": root}).as_row(),
            ref=ref,
            index=index,
            root=root,
        )
        for index, ref in enumerate(ref_rows)
    ]


def _hardgates(root: Path, decisions: Sequence[Mapping[str, Any]], refs: Sequence[LadderOpeningRef]) -> dict[str, dict[str, str]]:
    gate_statuses = _gate_statuses(root, decisions, refs=refs)
    return {
        "SL-HG1-evidence-provenance": {
            "status": gate_statuses["SL-HG1-evidence-provenance"],
            "pointer": EVIDENCE_PROVENANCE_POINTER,
        },
        "SL-HG2-construct-validity": {
            "status": gate_statuses["SL-HG2-construct-validity"],
            "pointer": CONSTRUCT_VALIDITY_POINTER,
        },
        "SL-HG3-owner-decision": {
            "status": gate_statuses["SL-HG3-owner-decision"],
            "pointer": f"{JSON_ARTIFACT}:$.levels[*].owner_decision_pointer",
        },
        "SL-HG4-split-separation": {
            "status": gate_statuses["SL-HG4-split-separation"],
            "pointer": f"{JSON_ARTIFACT}:$.levels",
        },
        "SL-HG5-no-injected-opening": {
            "status": "fail" if any(_old_injected_ladder(root, ref) is not None for ref in refs) else "pass",
            "pointer": DGT_SCALING_LADDER_POINTER,
        },
    }


def build_scaling_ladder_payload(
    *,
    root: Path,
    generated_at: str | None = None,
    refs: Sequence[LadderOpeningRef] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else _now()
    ref_rows = list(default_ladder_refs() if refs is None else refs)
    decisions = _expected_level_rows(root, ref_rows)
    boundary_ledger = [
        _boundary_row(row, recorded_at=timestamp)
        for row in decisions
        if row["state"] == "boundary"
    ]
    hardgates = _hardgates(root, decisions, ref_rows)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": PRODUCER,
        "source_artifacts": {
            "index": INDEX_ARTIFACT,
            "dgt": DGT_JSON_ARTIFACT,
            "l0_controls": DGT_L0_CONTROLS_JSON_ARTIFACT,
            "l1_controls": DGT_L1_CONTROLS_JSON_ARTIFACT,
            "construct_validity": DGT_L1_CONTROLS_JSON_ARTIFACT,
        },
        "consumer_pointers": {
            "levels_pointer": f"{JSON_ARTIFACT}:$.levels",
            "boundary_ledger_pointer": f"{JSON_ARTIFACT}:$.boundary_ledger",
            "hardgates_pointer": f"{JSON_ARTIFACT}:$.hardgates",
        },
        "levels": decisions,
        "boundary_ledger": boundary_ledger,
        "hardgates": hardgates,
        "not_claimed": list(NOT_CLAIMED),
    }
    validate_scaling_ladder_payload(payload, root=root, refs=ref_rows)
    return payload


def _validate_pointer_resolves(root: Path, payload: Mapping[str, Any], pointer: str, field: str) -> None:
    split = split_artifact_pointer(pointer)
    if split is None:
        raise ValueError(f"scaling ladder pointer field malformed: {field}")
    artifact, _local = split
    if artifact == JSON_ARTIFACT:
        if _resolve_payload_or_artifact(root, payload, pointer) is None:
            raise ValueError(f"scaling ladder pointer field unresolved: {field}: {pointer}")
        return
    if resolve_artifact_pointer(root, pointer) is None:
        raise ValueError(f"scaling ladder pointer field unresolved: {field}: {pointer}")


def _expected_hg5_status(root: Path, refs: Sequence[LadderOpeningRef] | None = None) -> str:
    ref_rows = default_ladder_refs() if refs is None else refs
    return "fail" if any(_old_injected_ladder(root, ref) is not None for ref in ref_rows) else "pass"


def _validate_owner_recomputed_payload(
    payload: Mapping[str, Any],
    *,
    root: Path,
    refs: Sequence[LadderOpeningRef] | None = None,
) -> None:
    ref_rows = list(default_ladder_refs() if refs is None else refs)
    expected_levels = _expected_level_rows(root, ref_rows)
    actual_levels = payload.get("levels")
    if actual_levels != expected_levels:
        raise ValueError("scaling ladder level owner projection mismatch")
    expected_boundary = [
        _boundary_row(row, recorded_at=str(payload["generated_at"]))
        for row in expected_levels
        if row["state"] == "boundary"
    ]
    if payload.get("boundary_ledger") != expected_boundary:
        raise ValueError("scaling ladder boundary ledger owner projection mismatch")
    expected_hardgates = _hardgates(root, expected_levels, ref_rows)
    if payload.get("hardgates") != expected_hardgates:
        raise ValueError("scaling ladder hardgate owner projection mismatch")


def _validate_contract_cell(
    *,
    root: Path,
    row: Mapping[str, Any],
    index: int,
    contract_name: str,
    contract: Mapping[str, Any],
) -> None:
    field_by_contract = {contract: field for field, contract in _CONTRACTS_BY_FIELD.items()}
    required_pointer = contract["required_pointer"]
    resolution_status = contract["resolution_status"]
    actual_status, _value = _resolve(root, required_pointer)
    if resolution_status != actual_status:
        raise ValueError(f"scaling ladder owner contract resolution mismatch: {index}: {contract_name}")
    field = field_by_contract[contract_name]
    expected_pointer = required_pointer if actual_status == "resolved" else _contract_pointer(index, contract_name)
    if row[field] != expected_pointer:
        raise ValueError(f"scaling ladder owner contract pointer mismatch: {index}: {field}")


def validate_scaling_ladder_payload(
    payload: Mapping[str, Any],
    *,
    root: Path | None = None,
    refs: Sequence[LadderOpeningRef] | None = None,
) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "source_artifacts",
        "levels",
        "boundary_ledger",
        "hardgates",
        "not_claimed",
    }
    missing = required - set(payload)
    if missing:
        raise ValueError(f"scaling ladder payload missing keys: {sorted(missing)}")
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("scaling ladder schema mismatch")
    if not isinstance(payload.get("generated_at"), str) or not payload["generated_at"]:
        raise ValueError("scaling ladder generated_at must be a non-empty string")
    levels = payload.get("levels")
    if not isinstance(levels, list) or not levels:
        raise ValueError("scaling ladder levels must be a non-empty list")
    expected_level_keys = {
        "level_id",
        "state",
        "reason",
        "owner_decision_pointer",
        "evidence_provenance_pointer",
        "construct_validity_pointer",
        "split_winnability_pointer",
        "separation_pointer",
        "source_report_pointer",
        "boundary_ledger_pointer",
        "owner_contracts",
    }
    for index, row in enumerate(levels):
        if not isinstance(row, Mapping) or set(row) != expected_level_keys:
            raise ValueError(f"scaling ladder level row schema mismatch: {index}")
        if row["state"] not in ALLOWED_STATES:
            raise ValueError(f"scaling ladder invalid state: {row['state']}")
        if row["reason"] not in ALLOWED_REASONS:
            raise ValueError(f"scaling ladder invalid reason: {row['reason']}")
        contracts = row["owner_contracts"]
        if not isinstance(contracts, Mapping) or set(contracts) != set(_CONTRACTS_BY_FIELD.values()):
            raise ValueError(f"scaling ladder owner contract schema mismatch: {index}")
        for contract_name, contract in contracts.items():
            if not isinstance(contract, Mapping) or set(contract) != {"required_pointer", "resolution_status"}:
                raise ValueError(f"scaling ladder owner contract cell schema mismatch: {index}")
            if not isinstance(contract["required_pointer"], str) or not contract["required_pointer"]:
                raise ValueError(f"scaling ladder owner contract required pointer invalid: {index}")
            if contract["resolution_status"] not in {"resolved", "missing-pointer", "unresolved-pointer"}:
                raise ValueError(f"scaling ladder owner contract resolution invalid: {index}")
            if root is not None:
                _validate_contract_cell(
                    root=root,
                    row=row,
                    index=index,
                    contract_name=str(contract_name),
                    contract=contract,
                )
        for field in expected_level_keys - {"level_id", "state", "reason", "owner_contracts"}:
            if not isinstance(row[field], str) or not row[field]:
                raise ValueError(f"scaling ladder pointer field invalid: {field}")
            if root is not None:
                _validate_pointer_resolves(root, payload, row[field], field)
    boundary = payload.get("boundary_ledger")
    if not isinstance(boundary, list):
        raise ValueError("scaling ladder boundary ledger must be a list")
    expected_boundary_keys = {
        "level_id",
        "prior_state",
        "new_state",
        "reason",
        "failed_contract_pointer",
        "owner_pointer",
        "recorded_at",
    }
    for index, row in enumerate(boundary):
        if not isinstance(row, Mapping) or set(row) != expected_boundary_keys:
            raise ValueError(f"scaling ladder boundary row schema mismatch: {index}")
        if row["new_state"] not in ALLOWED_STATES or row["reason"] not in ALLOWED_REASONS:
            raise ValueError("scaling ladder boundary row status invalid")
    hardgates = payload.get("hardgates")
    if not isinstance(hardgates, Mapping) or not hardgates:
        raise ValueError("scaling ladder hardgates must be a non-empty object")
    for name, gate in hardgates.items():
        if not isinstance(name, str) or not isinstance(gate, Mapping):
            raise ValueError("scaling ladder hardgate invalid")
        if gate.get("status") not in {"pass", "fail"} or not isinstance(gate.get("pointer"), str):
            raise ValueError("scaling ladder hardgate fields invalid")
    if root is not None:
        expected_statuses = _gate_statuses(root, _expected_level_rows(root, refs), refs=refs)
        expected_statuses["SL-HG5-no-injected-opening"] = _expected_hg5_status(root, refs=refs)
        if set(hardgates) != set(expected_statuses):
            raise ValueError("scaling ladder hardgate set mismatch")
        for name, expected_status in expected_statuses.items():
            if hardgates[name].get("status") != expected_status:
                raise ValueError(f"scaling ladder hardgate status mismatch: {name}")
        _validate_owner_recomputed_payload(payload, root=root, refs=refs)
    not_claimed = payload.get("not_claimed")
    if not isinstance(not_claimed, list) or not all(isinstance(item, str) for item in not_claimed):
        raise ValueError("scaling ladder not_claimed must be string list")


def render_scaling_ladder_markdown(payload: Mapping[str, Any]) -> str:
    validate_scaling_ladder_payload(payload)
    lines = [
        "# Scaling Ladder",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Schema: `{payload['schema_id']}`",
        "",
        "## Levels",
        "",
        "| level | state | reason | owner decision | provenance | construct validity | split | separation |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["levels"]:
        lines.append(
            "| "
            f"`{row['level_id']}` | "
            f"`{row['state']}` | "
            f"`{row['reason']}` | "
            f"`{row['owner_decision_pointer']}` | "
            f"`{row['evidence_provenance_pointer']}` | "
            f"`{row['construct_validity_pointer']}` | "
            f"`{row['split_winnability_pointer']}` | "
            f"`{row['separation_pointer']}` |"
        )
    lines.extend(["", "## Boundary Ledger", ""])
    if payload["boundary_ledger"]:
        lines.extend(["| level | prior | current | reason | failed contract |", "| --- | --- | --- | --- | --- |"])
        for row in payload["boundary_ledger"]:
            lines.append(
                "| "
                f"`{row['level_id']}` | "
                f"`{row['prior_state']}` | "
                f"`{row['new_state']}` | "
                f"`{row['reason']}` | "
                f"`{row['failed_contract_pointer']}` |"
            )
    else:
        lines.append("- No boundary rows.")
    lines.extend(["", "## Hardgates", "", "| gate | status | pointer |", "| --- | --- | --- |"])
    for name, gate in payload["hardgates"].items():
        lines.append(f"| `{name}` | `{gate['status']}` | `{gate['pointer']}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    validate_scaling_ladder_payload(payload)
    json_path = root / JSON_ARTIFACT
    md_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(dict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_scaling_ladder_markdown(payload), encoding="utf-8")
