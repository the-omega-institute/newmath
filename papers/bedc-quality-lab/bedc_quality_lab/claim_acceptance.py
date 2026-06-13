"""Acceptance evidence gates for positive claim verdicts."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from bedc_quality_lab.artifact_freshness import ScorecardSnapshot
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer, split_artifact_pointer


@dataclass(frozen=True)
class PositiveClaimEvidenceResult:
    ok: bool
    missing_key: str | None
    ledger_pointer: str
    reason: str


def _pass(ledger_pointer: str) -> PositiveClaimEvidenceResult:
    return PositiveClaimEvidenceResult(ok=True, missing_key=None, ledger_pointer=ledger_pointer, reason="pass")


def _fail(missing_key: str, ledger_pointer: str) -> PositiveClaimEvidenceResult:
    return PositiveClaimEvidenceResult(
        ok=False,
        missing_key=missing_key,
        ledger_pointer=ledger_pointer,
        reason=f"positive-acceptance-evidence-missing:{missing_key}",
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
