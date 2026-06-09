"""Run-local architecture mutation draft projection."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .capsule import CLAIM_CAPSULE_JSON_ARTIFACT
from .pointers import resolve_artifact_pointer, split_artifact_pointer


ARCHITECTURE_MUTATION_DRAFT_RUN_LOCAL_SCHEMA_ID = "bedc-quality-lab:architecture-mutation-draft-run-local"
CANONICAL_ROLE = "run_local_not_in_CANONICAL_REPORTS"
HARDGATES = {
    "AMB-HG1": "witness_basis_resolves",
    "AMB-HG2": "claim_capsule_resolves",
    "AMB-HG3": "pointer_only_no_witness_copy",
    "AMB-HG4": "board_admission_requires_pass",
}
FORBIDDEN_COPY_KEYS = frozenset(
    {
        "anti_triviality_status",
        "base_level",
        "classifier_reason",
        "classifier_reasons",
        "copied_negative_witness_body",
        "copied_witness",
        "debt_row",
        "discovery_level",
        "downgrade_reason",
        "effective_level",
        "hypothesis",
        "metrics",
        "negative_witness",
        "negative_witness_body",
        "raw_metrics",
        "terminal_verdict",
        "verdict",
        "what_was_learned",
        "witness_body",
        "witness_prose",
    }
)
ARCHITECTURE_MUTATION_CANDIDATE_FIELDS = frozenset(
    {
        "architecture_mutation_draft",
        "architecture_mutation_draft_id",
        "architecture_mutation_draft_pointer",
        "architecture_mutation_payload",
    }
)


@dataclass(frozen=True)
class GateResult:
    status: str
    reason: str
    pointers: tuple[str, ...] = ()


@dataclass(frozen=True)
class ArchitectureMutationDraft:
    draft_id: str
    status: str
    witness_basis_pointer: str
    claim_capsule_pointer: str
    hardgate_pointer: str
    hardgates: Mapping[str, Mapping[str, Any]]
    discovery_map_pointer: str | None = None
    negative_witness_summary_pointer: str | None = None

    def as_dict(self) -> dict[str, Any]:
        row = {
            "draft_id": self.draft_id,
            "kind": "architecture_mutation",
            "status": self.status,
            "witness_basis_pointer": self.witness_basis_pointer,
            "claim_capsule_pointer": self.claim_capsule_pointer,
            "hardgate_pointer": self.hardgate_pointer,
            "hardgates": {key: dict(value) for key, value in self.hardgates.items()},
        }
        if self.discovery_map_pointer:
            row["discovery_map_pointer"] = self.discovery_map_pointer
        if self.negative_witness_summary_pointer:
            row["negative_witness_summary_pointer"] = self.negative_witness_summary_pointer
        return row


def is_architecture_mutation_candidate(candidate: Mapping[str, Any]) -> bool:
    return (
        str(candidate.get("kind") or "") == "architecture_mutation"
        or candidate.get("schema_id") == ARCHITECTURE_MUTATION_DRAFT_RUN_LOCAL_SCHEMA_ID
        or bool(set(candidate) & ARCHITECTURE_MUTATION_CANDIDATE_FIELDS)
    )


def resolve_architecture_pointer(root: Path, pointer: str) -> Any:
    if split_artifact_pointer(pointer) is None:
        return None
    return resolve_artifact_pointer(root, pointer)


def _digest_id(*parts: str) -> str:
    digest = hashlib.sha256("\n".join(parts).encode("utf-8")).hexdigest()
    return f"amb:{digest[:16]}"


def _recursive_forbidden_keys(value: Any, *, path: tuple[str, ...] = ()) -> list[str]:
    found: set[str] = set()
    if isinstance(value, Mapping):
        for key, child in value.items():
            key_text = str(key)
            child_path = path + (key_text,)
            if key_text in FORBIDDEN_COPY_KEYS:
                found.add(".".join(child_path))
            found.update(_recursive_forbidden_keys(child, path=child_path))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            found.update(_recursive_forbidden_keys(child, path=path + (f"[{index}]",)))
    elif isinstance(value, str) and value in {"D0", "D1", "D2", "D3", "D4", "D5-O", "D5-M", "DN", "DR"}:
        found.add(".".join(path) or "$")
    return sorted(found)


def _pointer_from_row(row: Mapping[str, Any], *keys: str) -> str | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and split_artifact_pointer(value) is not None:
            return value
    return None


def _artifact_pointer_from_row(row: Mapping[str, Any], pointer_key: str) -> str | None:
    artifact = row.get("json_artifact")
    pointer = row.get(pointer_key)
    if isinstance(artifact, str) and isinstance(pointer, str) and pointer.startswith("$."):
        cell = f"{artifact}:{pointer}"
        if split_artifact_pointer(cell) is not None:
            return cell
    return None


def _default_claim_capsule_pointer() -> str:
    return f"{CLAIM_CAPSULE_JSON_ARTIFACT}:$"


def _hardgate_row(name: str, status: str, reason: str, pointers: Sequence[str] = ()) -> dict[str, Any]:
    return {
        "name": name,
        "status": status,
        "reason": reason,
        "pointers": list(pointers),
    }


def _draft_hardgates(
    *,
    root: Path,
    witness_basis_pointer: str | None,
    claim_capsule_pointer: str | None,
    hardgate_pointer: str | None,
    row: Mapping[str, Any],
) -> dict[str, dict[str, Any]]:
    copied = _recursive_forbidden_keys(row)
    witness_ok = bool(witness_basis_pointer and resolve_architecture_pointer(root, witness_basis_pointer) is not None)
    capsule_ok = bool(claim_capsule_pointer and resolve_architecture_pointer(root, claim_capsule_pointer) is not None)
    pointer_only = not copied
    board_ok = witness_ok and capsule_ok and pointer_only and bool(hardgate_pointer)
    return {
        "AMB-HG1": _hardgate_row(
            HARDGATES["AMB-HG1"],
            "pass" if witness_ok else "fail",
            "witness basis pointer resolves" if witness_ok else "witness basis pointer is missing or unresolved",
            [witness_basis_pointer] if witness_basis_pointer else [],
        ),
        "AMB-HG2": _hardgate_row(
            HARDGATES["AMB-HG2"],
            "pass" if capsule_ok else "fail",
            "claim capsule pointer resolves" if capsule_ok else "claim capsule pointer is missing or unresolved",
            [claim_capsule_pointer] if claim_capsule_pointer else [],
        ),
        "AMB-HG3": _hardgate_row(
            HARDGATES["AMB-HG3"],
            "pass" if pointer_only else "fail",
            "row is pointer-only" if pointer_only else "row copies witness body cells",
        ),
        "AMB-HG4": _hardgate_row(
            HARDGATES["AMB-HG4"],
            "pass" if board_ok else "fail",
            "board admission may proceed" if board_ok else "board admission requires passing witness and pointer gates",
            [pointer for pointer in (witness_basis_pointer, claim_capsule_pointer, hardgate_pointer) if pointer],
        ),
    }


def _status_from_hardgates(hardgates: Mapping[str, Mapping[str, Any]]) -> str:
    return "queue_admissible" if all(gate.get("status") == "pass" for gate in hardgates.values()) else "blocked"


def _draft_from_witness_row(root: Path, row: Mapping[str, Any]) -> ArchitectureMutationDraft:
    witness_basis_pointer = _pointer_from_row(
        row,
        "witness_basis_pointer",
        "source_witness_pointer",
        "negative_report_pointer",
        "source",
        "ledger_pointer",
    )
    claim_capsule_pointer = _pointer_from_row(row, "claim_capsule_pointer") or _default_claim_capsule_pointer()
    hardgate_pointer = (
        _pointer_from_row(row, "hardgate_pointer")
        or _artifact_pointer_from_row(row, "failed_gate")
        or witness_basis_pointer
        or ""
    )
    discovery_map_pointer = _pointer_from_row(row, "discovery_map_pointer")
    negative_summary_pointer = _pointer_from_row(row, "negative_witness_summary_pointer", "summary_pointer")
    hardgates = _draft_hardgates(
        root=root,
        witness_basis_pointer=witness_basis_pointer,
        claim_capsule_pointer=claim_capsule_pointer,
        hardgate_pointer=hardgate_pointer,
        row=row,
    )
    status = _status_from_hardgates(hardgates)
    return ArchitectureMutationDraft(
        draft_id=_digest_id(witness_basis_pointer or "missing", claim_capsule_pointer or "missing", hardgate_pointer or "missing"),
        status=status,
        witness_basis_pointer=witness_basis_pointer or "",
        claim_capsule_pointer=claim_capsule_pointer or "",
        hardgate_pointer=hardgate_pointer or "",
        discovery_map_pointer=discovery_map_pointer,
        negative_witness_summary_pointer=negative_summary_pointer,
        hardgates=hardgates,
    )


def _candidate_pointer(candidate_or_draft: Mapping[str, Any], key: str) -> str | None:
    value = candidate_or_draft.get(key)
    if isinstance(value, str):
        return value
    nested = candidate_or_draft.get("architecture_mutation_draft")
    if isinstance(nested, Mapping):
        nested_value = nested.get(key)
        if isinstance(nested_value, str):
            return nested_value
    pointers = candidate_or_draft.get("pointers")
    if isinstance(pointers, Mapping):
        pointer_value = pointers.get(key)
        if isinstance(pointer_value, str):
            return pointer_value
    return None


def require_witness_basis(candidate_or_draft: Mapping[str, Any], root: Path) -> GateResult:
    witness_basis_pointer = _candidate_pointer(candidate_or_draft, "witness_basis_pointer")
    if not witness_basis_pointer:
        return GateResult(status="fail", reason="missing_witness_basis", pointers=())
    if split_artifact_pointer(witness_basis_pointer) is None:
        return GateResult(status="fail", reason="AMB-HG1", pointers=(witness_basis_pointer,))
    if resolve_architecture_pointer(root, witness_basis_pointer) is None:
        return GateResult(status="fail", reason="AMB-HG1", pointers=(witness_basis_pointer,))
    claim_capsule_pointer = _candidate_pointer(candidate_or_draft, "claim_capsule_pointer") or _default_claim_capsule_pointer()
    if split_artifact_pointer(claim_capsule_pointer) is None:
        return GateResult(status="fail", reason="AMB-HG2", pointers=(witness_basis_pointer, claim_capsule_pointer))
    if resolve_architecture_pointer(root, claim_capsule_pointer) is None:
        return GateResult(status="fail", reason="AMB-HG2", pointers=(witness_basis_pointer, claim_capsule_pointer))
    copied = _recursive_forbidden_keys(
        candidate_or_draft.get("architecture_mutation_draft", candidate_or_draft)
    )
    if copied:
        return GateResult(status="fail", reason="AMB-HG3", pointers=(witness_basis_pointer,))
    return GateResult(status="pass", reason="pass", pointers=(witness_basis_pointer, claim_capsule_pointer))


def _rows_from_summary(negative_witness_summary: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    rows = negative_witness_summary.get("rows")
    if isinstance(rows, list):
        return [row for row in rows if isinstance(row, Mapping)]
    return []


def build_architecture_mutation_drafts(
    root: Path,
    generated_at: str,
    witness_rows: Sequence[Mapping[str, Any]],
    discovery_map: Mapping[str, Any],
    negative_witness_summary: Mapping[str, Any],
) -> dict[str, Any]:
    del discovery_map
    source_rows = list(witness_rows) or _rows_from_summary(negative_witness_summary)
    drafts = [_draft_from_witness_row(root, row).as_dict() for row in source_rows if isinstance(row, Mapping)]
    queue_rows = [row for row in drafts if row["status"] == "queue_admissible"]
    status = "pass" if queue_rows else "blocked"
    payload = {
        "schema_id": ARCHITECTURE_MUTATION_DRAFT_RUN_LOCAL_SCHEMA_ID,
        "canonical_role": CANONICAL_ROLE,
        "generated_at": generated_at,
        "producer": "bedc_quality_lab.discovery_compiler.architecture_mutation",
        "status": status,
        "hardgate_names": dict(HARDGATES),
        "row_count": len(drafts),
        "queue_admissible_count": len(queue_rows),
        "rows": drafts,
        "queue_admissible_rows": queue_rows,
    }
    json.dumps(payload, sort_keys=True)
    return payload
