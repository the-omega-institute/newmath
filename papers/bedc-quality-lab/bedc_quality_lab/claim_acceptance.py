"""Acceptance evidence gates for positive claim verdicts."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.artifact_freshness import ScorecardSnapshot
from bedc_quality_lab.discovery_compiler.pointers import (
    normalize_artifact_pointer,
    pointer_value,
    resolve_artifact_pointer,
    split_artifact_pointer,
)


CLAIM_FIRST_CARD_IDS = (
    "claim",
    "task-target",
    "data",
    "training-authenticity",
    "statistical",
)


@dataclass(frozen=True)
class PositiveClaimEvidenceResult:
    ok: bool
    missing_key: str | None
    ledger_pointer: str
    reason: str


@dataclass(frozen=True)
class ClaimFirstPointerCheck:
    card_id: str
    pointer: str
    status: str
    reason: str
    resolved_status: str | None = None
    hardgate_status: str | None = None

    def to_json(self) -> dict[str, Any]:
        return {
            "card_id": self.card_id,
            "pointer": self.pointer,
            "status": self.status,
            "reason": self.reason,
            "resolved_status": self.resolved_status,
            "hardgate_status": self.hardgate_status,
        }


def _pass(ledger_pointer: str) -> PositiveClaimEvidenceResult:
    return PositiveClaimEvidenceResult(ok=True, missing_key=None, ledger_pointer=ledger_pointer, reason="pass")


def _fail(missing_key: str, ledger_pointer: str) -> PositiveClaimEvidenceResult:
    return PositiveClaimEvidenceResult(
        ok=False,
        missing_key=missing_key,
        ledger_pointer=ledger_pointer,
        reason=f"positive-acceptance-evidence-missing:{missing_key}",
    )


def _claim_first_fail(card_id: str, ledger_pointer: str) -> PositiveClaimEvidenceResult:
    return PositiveClaimEvidenceResult(
        ok=False,
        missing_key=f"claim-first:{card_id}",
        ledger_pointer=ledger_pointer,
        reason=f"positive-acceptance-evidence-missing:claim-first:{card_id}",
    )


def _non_empty(value: Any) -> bool:
    if value is None or value == "":
        return False
    if isinstance(value, (list, tuple, dict, set)):
        return bool(value)
    return True


def _artifact_pointer(artifact: str, pointer: str | None) -> str | None:
    if not pointer:
        return None
    if pointer.startswith("$"):
        return f"{artifact}:{pointer}"
    if ":" in pointer:
        return pointer
    return None


def _string_pointer(value: Any) -> str | None:
    return value if isinstance(value, str) and normalize_artifact_pointer(value) is not None else None


def _claim_capsule_pointer(payload: Mapping[str, Any]) -> str | None:
    ref = payload.get("claim_capsule_ref")
    if isinstance(ref, str) and ref:
        return f"{ref}:$" if split_artifact_pointer(ref) is None else ref
    if isinstance(ref, Mapping):
        artifact = ref.get("artifact")
        pointer = ref.get("pointer", "$")
        if isinstance(artifact, str) and isinstance(pointer, str):
            return f"{artifact}:{pointer}"
        capsule = ref.get("capsule")
        if isinstance(capsule, Mapping):
            return "$.claim_capsule_ref.capsule"
    capsule = payload.get("claim_capsule")
    if isinstance(capsule, Mapping):
        artifact = capsule.get("artifact")
        pointer = capsule.get("pointer", "$")
        if isinstance(artifact, str) and isinstance(pointer, str):
            return f"{artifact}:{pointer}"
        return "$.claim_capsule"
    if isinstance(capsule, str) and capsule:
        return f"{capsule}:$" if split_artifact_pointer(capsule) is None else capsule
    run_artifacts = payload.get("run_artifacts")
    if isinstance(run_artifacts, Mapping):
        artifact = run_artifacts.get("claim_capsule")
        if isinstance(artifact, str) and artifact:
            return f"{artifact}:$"
    config = payload.get("config")
    if isinstance(config, Mapping):
        artifact = config.get("claim_capsule_artifact")
        if isinstance(artifact, str) and artifact:
            return f"{artifact}:$"
    return None


def _claim_capsule_resolves(root: Path, payload: Mapping[str, Any], capsule_pointer: str | None) -> bool:
    if not capsule_pointer:
        return False
    if capsule_pointer.startswith("$."):
        return pointer_value(payload, capsule_pointer) is not None
    return resolve_artifact_pointer(root, capsule_pointer) is not None


def _mapping_status(value: Any) -> str | None:
    if not isinstance(value, Mapping):
        return None
    for key in ("status", "hardgate_status", "review_status", "promotion_readiness", "training_evidence_status"):
        status = value.get(key)
        if isinstance(status, str):
            return status
    return None


def _blocked_status(value: Any) -> str | None:
    if not isinstance(value, Mapping):
        return None
    status = _mapping_status(value)
    if isinstance(status, str) and status.lower() in {
        "blocked",
        "fail",
        "failed",
        "missing",
        "not-ready",
        "tainted",
        "empirical_training_tainted",
        "training_evidence_absent",
    }:
        return status
    if value.get("taint_status") not in {None, "untainted"}:
        return str(value.get("taint_status"))
    allowed = value.get("allowed_claim_kinds")
    if isinstance(allowed, Sequence) and not isinstance(allowed, (str, bytes)) and "projection_only" in allowed:
        return "projection_only"
    return None


def _hardgates_pass(value: Any) -> bool:
    if not isinstance(value, Mapping):
        return True
    hardgates = value.get("hardgates")
    if not isinstance(hardgates, Mapping):
        return True
    for row in hardgates.values():
        if isinstance(row, Mapping) and row.get("status") != "pass":
            return False
        if isinstance(row, str) and row != "pass":
            return False
    return True


def _cell_passes(value: Any) -> bool:
    if value is None:
        return False
    blocked = _blocked_status(value)
    if blocked is not None:
        return False
    return _hardgates_pass(value)


def _card_cell_passes(card_id: str, value: Any) -> bool:
    if not _cell_passes(value):
        return False
    if not isinstance(value, Mapping):
        return True
    if card_id == "data":
        return value.get("evidence_type") not in {"empirical_training_tainted"}
    if card_id == "training-authenticity":
        return value.get("training_evidence_status") == "empirical_training_clean"
    if card_id == "statistical":
        return value.get("allowed_for_empirical_claim") is True and value.get("source_type") == "measured_training"
    return True


def _claim_first_check(root: Path, card_id: str, pointer: str) -> ClaimFirstPointerCheck:
    resolved = resolve_artifact_pointer(root, pointer)
    if resolved is None:
        return ClaimFirstPointerCheck(card_id, pointer, "fail", "owner pointer does not resolve")
    status = _mapping_status(resolved)
    if not _card_cell_passes(card_id, resolved):
        return ClaimFirstPointerCheck(card_id, pointer, "fail", "owner status or hardgate blocks promotion", status, "fail")
    return ClaimFirstPointerCheck(card_id, pointer, "pass", "owner pointer passes", status, "pass")


def _evidence_owner(root: Path, evidence_pointer: str | None) -> Any:
    if not evidence_pointer:
        return None
    return resolve_artifact_pointer(root, evidence_pointer)


def claim_first_pointer_checks(
    root: Path,
    *,
    spec: Any,
    discovery_row: Mapping[str, Any],
    payload: Mapping[str, Any],
    scorecard_snapshot: ScorecardSnapshot,
) -> tuple[ClaimFirstPointerCheck, ...]:
    artifact = str(getattr(spec, "json_artifact"))
    claim_capsule = _claim_capsule_pointer(payload)
    claim_pointer = _artifact_pointer(artifact, getattr(spec, "positive_claim_pointer", None))
    task_pointer = (
        _artifact_pointer(artifact, getattr(spec, "control_pointer", None))
        or _artifact_pointer(artifact, getattr(spec, "no_control_rationale_pointer", None))
        or _artifact_pointer(artifact, getattr(spec, "scope_pointer", None))
    )
    evidence_pointer = _string_pointer(discovery_row.get("evidence_provenance_pointer"))
    data_pointer = evidence_pointer
    evidence_owner = _evidence_owner(root, evidence_pointer)
    producer_pointer = (
        evidence_owner.get("producer_training_audit_pointer")
        if isinstance(evidence_owner, Mapping) and isinstance(evidence_owner.get("producer_training_audit_pointer"), str)
        else None
    )
    metric_pointers = (
        evidence_owner.get("metric_provenance_pointers")
        if (
            isinstance(evidence_owner, Mapping)
            and isinstance(evidence_owner.get("metric_provenance_pointers"), Sequence)
            and not isinstance(evidence_owner.get("metric_provenance_pointers"), (str, bytes))
        )
        else ()
    )
    metric_pointer = next((item for item in metric_pointers if isinstance(item, str)), None)
    pointers = {
        "claim": claim_capsule or claim_pointer,
        "task-target": task_pointer,
        "data": data_pointer,
        "training-authenticity": producer_pointer,
        "statistical": metric_pointer,
    }
    checks: list[ClaimFirstPointerCheck] = []
    for card_id in CLAIM_FIRST_CARD_IDS:
        pointer = pointers.get(card_id)
        if not pointer:
            checks.append(ClaimFirstPointerCheck(card_id, f"{artifact}:$", "fail", "owner pointer is missing"))
            continue
        checks.append(_claim_first_check(root, card_id, pointer))
    return tuple(checks)


def _claim_first_result(
    root: Path,
    *,
    spec: Any,
    discovery_row: Mapping[str, Any],
    payload: Mapping[str, Any],
    scorecard_snapshot: ScorecardSnapshot,
) -> PositiveClaimEvidenceResult:
    checks = claim_first_pointer_checks(
        root,
        spec=spec,
        discovery_row=discovery_row,
        payload=payload,
        scorecard_snapshot=scorecard_snapshot,
    )
    for check in checks:
        if check.status != "pass":
            return _claim_first_fail(check.card_id, check.pointer)
    return _pass(next(check.pointer for check in checks if check.card_id == "claim"))


def validate_positive_claim_evidence(
    root: Path,
    *,
    spec: Any,
    discovery_row: Mapping[str, Any],
    payload: Mapping[str, Any],
    scorecard_snapshot: ScorecardSnapshot,
) -> PositiveClaimEvidenceResult:
    if getattr(spec, "claim_promotion_eligible", True) is not True:
        artifact = str(getattr(spec, "json_artifact"))
        return _fail("claim_promotion_eligible", f"{artifact}:$")
    artifact = str(getattr(spec, "json_artifact"))
    control_pointer = getattr(spec, "control_pointer", None)
    no_control_pointer = getattr(spec, "no_control_rationale_pointer", None)
    control_cell = _artifact_pointer(artifact, control_pointer)
    no_control_cell = _artifact_pointer(artifact, no_control_pointer)
    if control_cell is None and no_control_cell is None:
        return _fail("control-or-no-control-rationale", f"{artifact}:$")
    if control_cell is not None and not _non_empty(resolve_artifact_pointer(root, control_cell)):
        if no_control_cell is None or not _non_empty(resolve_artifact_pointer(root, no_control_cell)):
            return _fail("control-or-no-control-rationale", control_cell)
    elif control_cell is None and not _non_empty(resolve_artifact_pointer(root, no_control_cell or "")):
        return _fail("control-or-no-control-rationale", no_control_cell or f"{artifact}:$")

    not_claimed_cell = _artifact_pointer(artifact, getattr(spec, "not_claimed_pointer", None))
    if not_claimed_cell is None or not _non_empty(resolve_artifact_pointer(root, not_claimed_cell)):
        return _fail("not_claimed", not_claimed_cell or f"{artifact}:$")

    positive_cell = _artifact_pointer(artifact, getattr(spec, "positive_claim_pointer", None))
    if positive_cell is None or not _non_empty(resolve_artifact_pointer(root, positive_cell)):
        return _fail("positive_claim", positive_cell or f"{artifact}:$")

    if not scorecard_snapshot.scorecard_hash:
        return _fail("scorecard_hash", scorecard_snapshot.scorecard_pointer)
    if scorecard_snapshot.scorecard_ready is not True:
        return _fail("scorecard_ready", scorecard_snapshot.scorecard_pointer)

    capsule_pointer = _claim_capsule_pointer(payload)
    if not _claim_capsule_resolves(root, payload, capsule_pointer):
        return _fail("claim_capsule", f"{artifact}:{capsule_pointer}" if capsule_pointer and capsule_pointer.startswith("$.") else capsule_pointer or f"{artifact}:$")

    claim_first = _claim_first_result(
        root,
        spec=spec,
        discovery_row=discovery_row,
        payload=payload,
        scorecard_snapshot=scorecard_snapshot,
    )
    if not claim_first.ok:
        return claim_first

    return _pass(positive_cell)


def validate_dn_owner_cell(root: Path, negative_report_pointer: str) -> PositiveClaimEvidenceResult:
    owner = resolve_artifact_pointer(root, negative_report_pointer)
    owners = [owner] if isinstance(owner, Mapping) else []
    split = split_artifact_pointer(negative_report_pointer)
    if split is not None:
        artifact, _pointer = split
        for pointer in ("$.dimension_mismatch_debt_transfer", "$.claim_capsule", "$"):
            candidate = resolve_artifact_pointer(root, f"{artifact}:{pointer}")
            if isinstance(candidate, Mapping):
                owners.append(candidate)
                capsule_pointer = _claim_capsule_pointer(candidate)
                if capsule_pointer:
                    capsule = resolve_artifact_pointer(root, capsule_pointer)
                    if isinstance(capsule, Mapping):
                        owners.append(capsule)
    if not owners:
        return _fail("negative_report_pointer", negative_report_pointer)
    if not any(isinstance(candidate.get("what_was_learned"), str) and candidate["what_was_learned"].strip() for candidate in owners):
        return _fail("what_was_learned", negative_report_pointer)
    return _pass(negative_report_pointer)
