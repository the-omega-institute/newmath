"""Shared U hardgate mechanics for run-local claim capsules."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer


FORBIDDEN_AUDIT_COLUMNS = (
    "terminal_verdict",
    "positive_claim",
    "arm_aggregates",
    "metrics",
)


def _status(value: bool) -> str:
    return "pass" if value else "fail"


def _as_mapping(value: Any) -> Mapping[str, Any] | None:
    return value if isinstance(value, Mapping) else None


def _as_sequence(value: Any) -> list[Any]:
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return list(value)
    return []


def _pointer(payload: Mapping[str, Any], pointer: str) -> Any:
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer)


def _load_json(root: Path, artifact: str) -> Mapping[str, Any] | None:
    path = root / artifact
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    return payload if isinstance(payload, Mapping) else None


def _resolves_artifact_pointer(root: Path, cell: str, payload: Mapping[str, Any]) -> bool:
    self_artifact = payload.get("self_artifact")
    if isinstance(self_artifact, str) and cell.startswith(f"{self_artifact}:"):
        _, pointer = cell.split(":", 1)
        if pointer == "$":
            return True
        return _pointer(payload, pointer) is not None
    resolved = resolve_artifact_pointer(root, cell)
    if resolved is not None:
        return True
    if cell.endswith(":$"):
        artifact = cell[:-2]
        return (root / artifact).exists()
    return False


def _forbidden_term_audit(value: Any) -> dict[str, Any]:
    text = json.dumps(value, sort_keys=True).lower().replace(" ", "-")
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": _status(not hits),
        "forbidden_positive_claim_terms": list(FORBIDDEN_POSITIVE_CLAIM_TERMS),
        "hits": hits,
    }


def _forbidden_column_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    public_surface = _as_mapping(payload.get("public_surface")) or _as_mapping(payload.get("canonical_sidecar")) or {}
    hits = [key for key in FORBIDDEN_AUDIT_COLUMNS if key in public_surface]
    return {
        "status": _status(not hits),
        "forbidden_columns": list(FORBIDDEN_AUDIT_COLUMNS),
        "hits": hits,
    }


def evaluate_u_hardgates(
    payload: Mapping[str, Any],
    *,
    root: Path,
    capsule_artifact: str,
    required_not_claimed: Sequence[str],
    cost_pointer: str,
    control_required: bool,
    positive_claim_pointer: str = "$.positive_claim",
    revocation_pointer: str = "$.revocation.rows",
) -> dict[str, Any]:
    """Evaluate generic U-HG1..8 mechanics without experiment-specific gates."""

    capsule = _load_json(root, capsule_artifact)
    if capsule is None and capsule_artifact == str(payload.get("self_artifact", "")):
        capsule = payload
    evidence_pointers = _as_sequence(payload.get("evidence_pointers"))
    pointer_checks = []
    for cell in evidence_pointers:
        pointer_cell = str(cell)
        pointer_checks.append(
            {
                "pointer": pointer_cell,
                "resolves": _resolves_artifact_pointer(root, pointer_cell, payload),
            }
        )
    if not evidence_pointers:
        source_artifacts = _as_mapping(payload.get("source_artifacts")) or {}
        for key, artifact in source_artifacts.items():
            if isinstance(artifact, str) and artifact.endswith(".json"):
                pointer_cell = f"{artifact}:$"
                pointer_checks.append(
                    {
                        "pointer": pointer_cell,
                        "source_key": key,
                        "resolves": _resolves_artifact_pointer(root, pointer_cell, payload),
                    }
                )
    not_claimed = [str(item) for item in _as_sequence(payload.get("not_claimed"))]
    missing_not_claimed = [item for item in required_not_claimed if item not in not_claimed]
    cost_value = _pointer(payload, cost_pointer)
    controls = _as_sequence(payload.get("control_rows"))
    if not controls:
        control_section = payload.get("controls")
        controls = _as_sequence(control_section) if isinstance(control_section, Sequence) else _as_sequence(_as_mapping(control_section).get("rows") if _as_mapping(control_section) else None)
    failed_gate = payload.get("failed_gate")
    what_was_learned = payload.get("what_was_learned")
    revocation_rows = _pointer(payload, revocation_pointer)
    if revocation_rows is None and capsule is not None:
        revocation_rows = _pointer(capsule, revocation_pointer)
    revocation_list = _as_sequence(revocation_rows)
    positive_claim = _pointer(payload, positive_claim_pointer)
    forbidden_claim = _forbidden_term_audit(positive_claim)
    forbidden_columns = _forbidden_column_audit(payload)
    claim_status = str(payload.get("claim_status", payload.get("status", ""))).lower()
    positive_level = str((_as_mapping(positive_claim) or {}).get("level", "")).upper()
    dn_requires_learning = claim_status in {"failed", "dn", "negative"} or positive_level == "DN"
    learning_ok = isinstance(what_was_learned, str) and bool(what_was_learned.strip())
    failed_gate_ok = isinstance(failed_gate, str) and bool(failed_gate.strip())
    gates = {
        "U-HG1": {
            "status": _status(capsule is not None),
            "capsule_artifact": capsule_artifact,
        },
        "U-HG2": {
            "status": _status(bool(pointer_checks) and all(row["resolves"] for row in pointer_checks)),
            "pointers": pointer_checks,
        },
        "U-HG3": {
            "status": _status(cost_value is not None),
            "cost_pointer": cost_pointer,
        },
        "U-HG4": {
            "status": _status(not missing_not_claimed),
            "required_not_claimed": list(required_not_claimed),
            "not_claimed": not_claimed,
            "missing": missing_not_claimed,
        },
        "U-HG5": {
            "status": _status((not control_required) or bool(controls)),
            "control_required": bool(control_required),
            "control_row_count": len(controls),
        },
        "U-HG6": {
            "status": _status(learning_ok and ((not dn_requires_learning) or failed_gate_ok)),
            "failed_gate": failed_gate,
            "dn_requires_failed_gate": dn_requires_learning,
            "what_was_learned_present": learning_ok,
        },
        "U-HG7": {
            "status": _status(bool(revocation_list)),
            "revocation_pointer": revocation_pointer,
            "revocation_row_count": len(revocation_list),
        },
        "U-HG8": {
            "status": _status(forbidden_claim["status"] == "pass" and forbidden_columns["status"] == "pass"),
            "positive_claim_audit": forbidden_claim,
            "forbidden_column_audit": forbidden_columns,
        },
    }
    failed = [name for name, row in gates.items() if row["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "failed_gates": failed,
        "gates": gates,
    }


__all__ = ["FORBIDDEN_AUDIT_COLUMNS", "evaluate_u_hardgates"]
