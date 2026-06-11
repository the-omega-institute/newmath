"""Canonical owner for scaling-ladder opening decisions."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
from collections.abc import Mapping, Sequence
from typing import Any

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer, split_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:scaling-ladder"
ARTIFACT_ID = "bedc-quality-lab:scaling-ladder"
PRODUCER = "scripts/run_scaling_ladder.py"
JSON_ARTIFACT = "reports/canonical/scaling-ladder.json"
MARKDOWN_ARTIFACT = "reports/canonical/scaling-ladder.md"
FINGERPRINT_ARTIFACT = "reports/canonical/scaling-ladder.fingerprint.json"
INDEX_ARTIFACT = "reports/canonical/index.json"
DGT_JSON_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
DGT_L0_CONTROLS_JSON_ARTIFACT = "reports/canonical/dgt-l0-controls.json"
DGT_L1_CONTROLS_JSON_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
DGT_BASE_UNDERTRAINING_JSON_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.json"
EVIDENCE_PROVENANCE_POINTER = f"{INDEX_ARTIFACT}:$.evidence_provenance"
CONSTRUCT_VALIDITY_POINTER = f"{DGT_BASE_UNDERTRAINING_JSON_ARTIFACT}:$.base_undertraining_audit.construct_validity"
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
    if construct.get("status") not in {"construct-valid", "pass"}:
        return False
    hardgates = construct.get("hardgates")
    if isinstance(hardgates, Mapping):
        return all(_mapping(row).get("status") == "pass" for row in hardgates.values())
    return True


def _decision_passes(value: Any) -> bool:
    decision = _mapping(value)
    status = decision.get("status")
    verdict = decision.get("verdict")
    if status in {"pass", "eligible", "scaling-evidence-eligible"}:
        return True
    if verdict in {"pass", "eligible", "scaling-evidence-eligible"}:
        return True
    if decision.get("decision") in {"pass", "eligible", "scaling-evidence-eligible"}:
        return True
    return False


def _split_winnable(value: Any) -> bool:
    split = _mapping(value)
    if split.get("winnable") is True:
        return True
    if split.get("status") in {"pass", "winnable"}:
        return True
    return False


def _separation_passes(value: Any) -> bool:
    separation = _mapping(value)
    if separation.get("status") == "pass":
        return True
    ci_low = separation.get("ci_low")
    if ci_low is None:
        ci_low = separation.get("ci95_low")
    if ci_low is None:
        ci_low = separation.get("ci_low_separation")
    return isinstance(ci_low, (int, float)) and not isinstance(ci_low, bool) and float(ci_low) > 0.0


def _old_injected_ladder(root: Path, ref: LadderOpeningRef) -> Mapping[str, Any] | None:
    legacy = resolve_artifact_pointer(root, f"{DGT_JSON_ARTIFACT}:$.scaling_ladder")
    if not isinstance(legacy, Mapping):
        return None
    opened = legacy.get("opened_levels")
    if isinstance(opened, Sequence) and not isinstance(opened, (str, bytes, bytearray)) and ref.level_id in opened:
        return legacy
    levels = legacy.get("levels")
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
    boundary_pointer = f"{JSON_ARTIFACT}:$.boundary_ledger[?level_id={ref.level_id}]"
    values: dict[str, Any] = {}
    for name, pointer in (
        ("evidence", ref.evidence_provenance_pointer),
        ("construct", ref.construct_validity_pointer),
        ("decision", ref.decision_pointer),
        ("split", ref.split_winnability_pointer),
        ("separation", ref.separation_pointer),
    ):
        status, value = _resolve(root, pointer)
        if status != "resolved":
            if _old_injected_ladder(root, ref) is not None:
                reason = "stale-or-injected"
                state = "boundary"
            else:
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
        values[name] = value
    provenance_reason = _reason_for_provenance(ref, values["evidence"])
    if provenance_reason is not None:
        state = "boundary" if _old_injected_ladder(root, ref) is not None else "closed"
        reason = "stale-or-injected" if state == "boundary" and provenance_reason == "projection-only" else provenance_reason
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
        "stale-or-injected": row["source_report_pointer"],
    }
    return {
        "level_id": row["level_id"],
        "prior_state": "open",
        "new_state": row["state"],
        "reason": row["reason"],
        "failed_contract_pointer": failed_pointer_by_reason.get(row["reason"], row["source_report_pointer"]),
        "owner_pointer": f"{JSON_ARTIFACT}:$.levels",
        "recorded_at": recorded_at,
    }


def build_scaling_ladder_payload(
    *,
    root: Path,
    generated_at: str | None = None,
    refs: Sequence[LadderOpeningRef] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else _now()
    ref_rows = list(default_ladder_refs() if refs is None else refs)
    decisions = [
        evaluate_ladder_opening(ref, {"root": root}).as_row()
        for ref in ref_rows
    ]
    boundary_ledger = [
        _boundary_row(row, recorded_at=timestamp)
        for row in decisions
        if row["state"] == "boundary"
    ]
    hardgates = {
        "SL-HG1-evidence-provenance": {
            "status": "pass" if all(row["reason"] not in {"missing-pointer", "unresolved-pointer", "non-measured-evidence", "projection-only"} for row in decisions) else "fail",
            "pointer": EVIDENCE_PROVENANCE_POINTER,
        },
        "SL-HG2-construct-validity": {
            "status": "pass" if all(row["reason"] != "construct-validity-failed" for row in decisions) else "fail",
            "pointer": CONSTRUCT_VALIDITY_POINTER,
        },
        "SL-HG3-owner-decision": {
            "status": "pass" if all(row["reason"] != "owner-negative" for row in decisions) else "fail",
            "pointer": f"{JSON_ARTIFACT}:$.levels[*].owner_decision_pointer",
        },
        "SL-HG4-split-separation": {
            "status": "pass" if all(row["reason"] not in {"split-not-winnable", "ci-low-separation-failed"} for row in decisions) else "fail",
            "pointer": f"{JSON_ARTIFACT}:$.levels",
        },
        "SL-HG5-no-injected-opening": {
            "status": "pass" if not boundary_ledger else "fail",
            "pointer": f"{DGT_JSON_ARTIFACT}:$.scaling_ladder",
        },
    }
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
            "construct_validity": DGT_BASE_UNDERTRAINING_JSON_ARTIFACT,
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
    validate_scaling_ladder_payload(payload)
    return payload


def validate_scaling_ladder_payload(payload: Mapping[str, Any]) -> None:
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
    }
    for index, row in enumerate(levels):
        if not isinstance(row, Mapping) or set(row) != expected_level_keys:
            raise ValueError(f"scaling ladder level row schema mismatch: {index}")
        if row["state"] not in ALLOWED_STATES:
            raise ValueError(f"scaling ladder invalid state: {row['state']}")
        if row["reason"] not in ALLOWED_REASONS:
            raise ValueError(f"scaling ladder invalid reason: {row['reason']}")
        for field in expected_level_keys - {"level_id", "state", "reason"}:
            if not isinstance(row[field], str) or not row[field]:
                raise ValueError(f"scaling ladder pointer field invalid: {field}")
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
