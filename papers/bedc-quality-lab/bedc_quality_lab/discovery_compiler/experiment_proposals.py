"""Experiment proposal sidecar for canonical discovery artifacts."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .map import load_validated_discovery_map_payload
from .pointers import resolve_artifact_pointer, split_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:experiment-proposals"
ARTIFACT_ID = "bedc-quality-lab:experiment-proposals"
CANONICAL_ROLE = "pointer_sidecar_not_CANONICAL_REPORTS"
JSON_ARTIFACT = "reports/canonical/experiment_proposals.json"
MARKDOWN_ARTIFACT = "reports/canonical/experiment_proposals.md"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
NEGATIVE_DISCOVERY_REPORTS_ARTIFACT = "reports/canonical/negative_discovery_reports.json"
GAP_HEAD_ATTRIBUTION_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"
SOURCE_ARTIFACTS = {
    "discovery_map": DISCOVERY_MAP_ARTIFACT,
    "negative_discovery_reports": NEGATIVE_DISCOVERY_REPORTS_ARTIFACT,
    "claim_verdicts": "reports/canonical/claim_verdicts.jsonl",
    "claim_capsule": "reports/canonical/claim_capsule.json",
    "gap_head_attribution_capsule": GAP_HEAD_ATTRIBUTION_ARTIFACT,
}
PROPOSAL_TYPES = frozenset(
    {
        "coverage_gap",
        "negative_discovery_followup",
        "d5m_blocked_followup",
    }
)
SOURCE_CLASS_ORDER = {
    "d5m_blocked_followup": 0,
    "negative_discovery_followup": 1,
    "coverage_gap": 2,
}
ROW_REQUIRED_KEYS = frozenset(
    {
        "proposal_id",
        "proposal_type",
        "source_kind",
        "source_pointer",
        "source_gap_pointer",
        "expected_failure_modes",
        "required_controls",
        "claim_capsule_draft",
        "not_claimed",
        "deterministic_toy_seed",
        "proposal_status",
        "audit_status",
    }
)
ROW_OPTIONAL_POINTER_KEYS = frozenset(
    {
        "coverage_cell_pointer",
        "negative_report_pointer",
        "failed_gate_pointer",
        "mechanism_evidence_pointer",
    }
)
ROW_ALLOWED_KEYS = ROW_REQUIRED_KEYS | ROW_OPTIONAL_POINTER_KEYS
DRAFT_REQUIRED_KEYS = frozenset(
    {
        "schema_id",
        "draft_id",
        "source_pointer",
        "source_gap_pointer",
        "claim_intent",
        "required_gates",
        "required_controls",
        "expected_failure_modes",
        "not_claimed",
    }
)
FORBIDDEN_KEYS = frozenset(
    {
        "terminal_verdict",
        "terminal_verdicts",
        "raw_metrics",
        "raw_metric_payload",
        "metrics",
        "metric",
        "classifier_reasons",
        "what_was_learned",
        "next_hypothesis",
        "hypothesis",
        "stop_reason",
        "downgrade_reason",
        "anti_triviality_gate_evidence",
        "bedc_gap_mapping",
        "owner_fact",
        "source_payload",
        "blocked_prose",
        "blocked_reason",
        "blockage_reason",
    }
)
FORBIDDEN_CLAIM_PHRASES = (
    "production ready",
    "production-ready",
    "production readiness",
    "global superiority",
    "globally superior",
    "state of the art",
    "state-of-the-art",
    "beats all",
    "dominates all",
)
COMMON_NOT_CLAIMED = (
    "No production readiness claim is made.",
    "No global superiority claim is made.",
)


def _timestamp(generated_at: str | None) -> str:
    return generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()


def _load_json(root: Path, artifact: str) -> dict[str, Any]:
    path = root / artifact
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"experiment proposal source must be a JSON object: {artifact}")
    return payload


def _write_json_atomic(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _digest(proposal_type: str, source_pointer: str) -> str:
    return hashlib.sha256(f"{proposal_type}\n{source_pointer}".encode("utf-8")).hexdigest()


def _proposal_id(proposal_type: str, source_pointer: str) -> str:
    return f"prop:{_digest(proposal_type, source_pointer)[:12]}"


def _toy_seed(proposal_type: str, source_pointer: str) -> int:
    return int(_digest(proposal_type, source_pointer)[12:20], 16)


def _artifact_pointer(artifact: str, pointer: Any) -> str | None:
    if isinstance(pointer, str) and pointer.startswith("$."):
        return f"{artifact}:{pointer}"
    if isinstance(pointer, str) and split_artifact_pointer(pointer) is not None:
        return pointer
    return None


def _pointer_resolves(root: Path, pointer: str | None) -> bool:
    return isinstance(pointer, str) and (
        pointer.startswith(f"{JSON_ARTIFACT}:") or resolve_artifact_pointer(root, pointer) is not None
    )


def _non_empty_string_list(value: Any, *, field: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise ValueError(f"experiment proposal {field} must be a non-empty list")
    rows: list[str] = []
    for item in value:
        if not isinstance(item, str) or not item.strip():
            raise ValueError(f"experiment proposal {field} must contain non-empty strings")
        rows.append(item)
    return rows


def _recursive_forbidden(value: Any, *, path: tuple[str, ...] = ()) -> list[str]:
    found: set[str] = set()
    if isinstance(value, Mapping):
        for key, item in value.items():
            key_text = str(key)
            child = path + (key_text,)
            if key_text in FORBIDDEN_KEYS:
                found.add(".".join(child))
            found.update(_recursive_forbidden(item, path=child))
    elif isinstance(value, list):
        for index, item in enumerate(value):
            found.update(_recursive_forbidden(item, path=path + (f"[{index}]",)))
    elif isinstance(value, str):
        if "not_claimed" in path:
            return sorted(found)
        lowered = value.lower()
        for phrase in FORBIDDEN_CLAIM_PHRASES:
            if phrase in lowered:
                found.add(".".join(path) or "$")
    return sorted(found)


def _claim_capsule_draft(
    *,
    proposal_id: str,
    source_pointer: str,
    source_gap_pointer: str,
    claim_intent: str,
    required_gates: Sequence[str],
    required_controls: Sequence[str],
    expected_failure_modes: Sequence[str],
    not_claimed: Sequence[str],
) -> dict[str, Any]:
    return {
        "schema_id": "bedc.quality.claim_capsule.draft",
        "draft_id": f"draft:{proposal_id.removeprefix('prop:')}",
        "source_pointer": source_pointer,
        "source_gap_pointer": source_gap_pointer,
        "claim_intent": claim_intent,
        "required_gates": list(required_gates),
        "required_controls": list(required_controls),
        "expected_failure_modes": list(expected_failure_modes),
        "not_claimed": list(not_claimed),
    }


def _row(
    *,
    proposal_type: str,
    source_kind: str,
    source_pointer: str,
    source_gap_pointer: str,
    expected_failure_modes: Sequence[str],
    required_controls: Sequence[str],
    required_gates: Sequence[str],
    claim_intent: str,
    extra: Mapping[str, str | None] | None = None,
) -> dict[str, Any]:
    proposal_id = _proposal_id(proposal_type, source_pointer)
    not_claimed = [
        *COMMON_NOT_CLAIMED,
        "This proposal is a bounded follow-up prompt, not a final claim capsule.",
    ]
    row: dict[str, Any] = {
        "proposal_id": proposal_id,
        "proposal_type": proposal_type,
        "source_kind": source_kind,
        "source_pointer": source_pointer,
        "source_gap_pointer": source_gap_pointer,
        "expected_failure_modes": list(expected_failure_modes),
        "required_controls": list(required_controls),
        "claim_capsule_draft": _claim_capsule_draft(
            proposal_id=proposal_id,
            source_pointer=source_pointer,
            source_gap_pointer=source_gap_pointer,
            claim_intent=claim_intent,
            required_gates=required_gates,
            required_controls=required_controls,
            expected_failure_modes=expected_failure_modes,
            not_claimed=not_claimed,
        ),
        "not_claimed": not_claimed,
        "deterministic_toy_seed": _toy_seed(proposal_type, source_pointer),
        "proposal_status": "proposed",
        "audit_status": "pointer-only",
    }
    for key, value in dict(extra or {}).items():
        if value is not None:
            row[key] = value
    return row


def _coverage_gap_rows(root: Path, discovery_map: Mapping[str, Any]) -> list[dict[str, Any]]:
    coverage = discovery_map.get("coverage_matrix")
    if not isinstance(coverage, Mapping):
        return []
    cells = coverage.get("cells")
    if not isinstance(cells, list):
        return []
    rows: list[dict[str, Any]] = []
    for index, cell in enumerate(cells):
        if not isinstance(cell, Mapping) or cell.get("hardgate_status") == "pass":
            continue
        source_pointer = f"{DISCOVERY_MAP_ARTIFACT}:$.coverage_matrix.cells[{index}]"
        source_gap_pointer = source_pointer
        rows.append(
            _row(
                proposal_type="coverage_gap",
                source_kind="coverage_matrix_cell",
                source_pointer=source_pointer,
                source_gap_pointer=source_gap_pointer,
                expected_failure_modes=[
                    "coverage pointer resolves but the cell remains non-passing",
                    "complete-set audit keeps the candidate at a boundary status",
                ],
                required_controls=[
                    "resolve only the coverage matrix cell and its owner pointer",
                    "preserve DN witness boundaries for negative cells",
                ],
                required_gates=["COV-HG1-owner", "COV-HG2-resolves", "COV-HG6-complete-set"],
                claim_intent="test whether this coverage gap can be closed under existing pointer owners",
                extra={
                    "coverage_cell_pointer": source_pointer,
                    "failed_gate_pointer": source_pointer,
                },
            )
        )
    return [row for row in rows if _pointer_resolves(root, row["source_pointer"])]


def _negative_discovery_rows(root: Path, reports: Mapping[str, Any]) -> list[dict[str, Any]]:
    owner_rows = reports.get("rows")
    if not isinstance(owner_rows, list):
        return []
    rows: list[dict[str, Any]] = []
    for index, owner in enumerate(owner_rows):
        if not isinstance(owner, Mapping):
            continue
        source_pointer = f"{NEGATIVE_DISCOVERY_REPORTS_ARTIFACT}:$.rows[{index}]"
        failed_gate_pointer = f"{source_pointer}.failed_gate"
        if not _pointer_resolves(root, source_pointer) or not _pointer_resolves(root, failed_gate_pointer):
            continue
        rows.append(
            _row(
                proposal_type="negative_discovery_followup",
                source_kind="negative_discovery_report",
                source_pointer=source_pointer,
                source_gap_pointer=failed_gate_pointer,
                expected_failure_modes=[
                    "negative owner gate remains reproducible",
                    "follow-up candidate fails matched-control promotion",
                ],
                required_controls=[
                    "resolve the negative owner row before interpreting the proposal",
                    "keep learned and control arms under the canonical cost boundary",
                ],
                required_gates=["negative-owner-row-resolves", "failed-gate-pointer-resolves"],
                claim_intent="probe whether the negative discovery has a bounded follow-up that still respects the failed gate",
                extra={
                    "negative_report_pointer": source_pointer,
                    "failed_gate_pointer": failed_gate_pointer,
                },
            )
        )
    return rows


def _d5m_rows(root: Path, discovery_map: Mapping[str, Any]) -> list[dict[str, Any]]:
    rows_payload = discovery_map.get("rows")
    if not isinstance(rows_payload, list):
        return []
    rows: list[dict[str, Any]] = []
    for index, item in enumerate(rows_payload):
        if not isinstance(item, Mapping):
            continue
        if item.get("mechanism_status") != "blocked" and item.get("mechanism_level") != "blocked":
            continue
        source_pointer = _artifact_pointer(str(item.get("json_artifact") or ""), item.get("mechanism_pointer"))
        mechanism_pointer = _artifact_pointer(str(item.get("json_artifact") or ""), item.get("mechanism_pointer"))
        failed_gate_pointer = _artifact_pointer(str(item.get("json_artifact") or ""), item.get("mechanism_failed_gate"))
        if source_pointer is None:
            source_pointer = f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}]"
        if failed_gate_pointer is None:
            failed_gate_pointer = f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}]"
        rows.append(
            _row(
                proposal_type="d5m_blocked_followup",
                source_kind="d5m_blocked_row",
                source_pointer=source_pointer,
                source_gap_pointer=failed_gate_pointer,
                expected_failure_modes=[
                    "mechanism evidence remains open",
                    "candidate mechanism fails closed under source audit",
                ],
                required_controls=[
                    "preserve the matched-control evidence boundary",
                    "separate mechanism proof evidence from operational readiness",
                ],
                required_gates=["mechanism-evidence-pointer-resolves", "mechanism-failed-gate-pointer-resolves"],
                claim_intent="test the blocked mechanism route without promoting operational evidence",
                extra={
                    "failed_gate_pointer": failed_gate_pointer,
                    "mechanism_evidence_pointer": mechanism_pointer,
                },
            )
        )
    return [row for row in rows if _pointer_resolves(root, row["source_pointer"])]


def build_experiment_proposals(root: Path, generated_at: str | None = None) -> dict[str, Any]:
    timestamp = _timestamp(generated_at)
    discovery_map = load_validated_discovery_map_payload(root, artifact=DISCOVERY_MAP_ARTIFACT)
    negative_reports = _load_json(root, NEGATIVE_DISCOVERY_REPORTS_ARTIFACT)
    rows = [
        *_d5m_rows(root, discovery_map),
        *_negative_discovery_rows(root, negative_reports),
        *_coverage_gap_rows(root, discovery_map),
    ]
    rows = sorted(
        rows,
        key=lambda item: (
            SOURCE_CLASS_ORDER.get(str(item["proposal_type"]), 99),
            str(item["source_pointer"]),
            str(item["proposal_type"]),
        ),
    )
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "canonical_role": CANONICAL_ROLE,
        "generated_at": timestamp,
        "source_artifacts": dict(SOURCE_ARTIFACTS),
        "row_count": len(rows),
        "rows": rows,
        "audit": {
            "status": "pass",
            "forbidden_source_fact_policy": "recursive-validator-enforced",
            "forbidden_claim_policy": "claim-text-validator-enforced-outside-not_claimed",
            "proposal_rows_pointer": f"{JSON_ARTIFACT}:$.rows",
            "source_artifacts_pointer": f"{JSON_ARTIFACT}:$.source_artifacts",
        },
    }
    return validate_experiment_proposal_payload(root, payload)


def _validate_draft(root: Path, draft: Mapping[str, Any]) -> dict[str, Any]:
    if set(draft) != DRAFT_REQUIRED_KEYS:
        missing = sorted(DRAFT_REQUIRED_KEYS - set(draft))
        extra = sorted(set(draft) - DRAFT_REQUIRED_KEYS)
        detail = []
        if missing:
            detail.append(f"missing {', '.join(missing)}")
        if extra:
            detail.append(f"extra {', '.join(extra)}")
        raise ValueError(f"claim capsule draft schema mismatch: {'; '.join(detail)}")
    if draft.get("schema_id") != "bedc.quality.claim_capsule.draft":
        raise ValueError("claim capsule draft schema_id mismatch")
    for key in ("draft_id", "source_pointer", "source_gap_pointer", "claim_intent"):
        if not isinstance(draft.get(key), str) or not str(draft[key]).strip():
            raise ValueError(f"claim capsule draft {key} must be a non-empty string")
    for key in ("source_pointer", "source_gap_pointer"):
        if not _pointer_resolves(root, str(draft[key])):
            raise ValueError(f"claim capsule draft unresolved pointer: {key}={draft[key]}")
    for key in ("required_gates", "required_controls", "expected_failure_modes", "not_claimed"):
        _non_empty_string_list(draft.get(key), field=f"claim_capsule_draft.{key}")
    copied = _recursive_forbidden(draft)
    if copied:
        raise ValueError(f"claim capsule draft contains forbidden source or claim cells: {', '.join(copied)}")
    return dict(draft)


def validate_experiment_proposal_payload(root: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("experiment proposal schema_id mismatch")
    if payload.get("artifact_id") != ARTIFACT_ID:
        raise ValueError("experiment proposal artifact_id mismatch")
    if payload.get("canonical_role") != CANONICAL_ROLE:
        raise ValueError("experiment proposal canonical_role mismatch")
    if not isinstance(payload.get("source_artifacts"), Mapping):
        raise ValueError("experiment proposal source_artifacts must be an object")
    rows = payload.get("rows")
    if not isinstance(rows, list):
        raise ValueError("experiment proposal rows must be a list")
    validated_rows: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, Mapping):
            raise ValueError("experiment proposal rows must be objects")
        copied = _recursive_forbidden(row)
        if copied:
            raise ValueError(f"experiment proposal copies source owner facts: {', '.join(copied)}")
        if set(row) - ROW_ALLOWED_KEYS:
            raise ValueError(f"experiment proposal row has unsupported keys: {', '.join(sorted(set(row) - ROW_ALLOWED_KEYS))}")
        missing = sorted(ROW_REQUIRED_KEYS - set(row))
        if missing:
            raise ValueError(f"experiment proposal row missing keys: {', '.join(missing)}")
        if row.get("proposal_type") not in PROPOSAL_TYPES:
            raise ValueError(f"unsupported proposal_type: {row.get('proposal_type')}")
        for key in ("proposal_id", "source_kind", "source_pointer", "source_gap_pointer", "proposal_status", "audit_status"):
            if not isinstance(row.get(key), str) or not str(row[key]).strip():
                raise ValueError(f"experiment proposal {key} must be a non-empty string")
        for key in ("source_pointer", "source_gap_pointer", *ROW_OPTIONAL_POINTER_KEYS):
            value = row.get(key)
            if value is not None and not _pointer_resolves(root, str(value)):
                raise ValueError(f"experiment proposal unresolved pointer: {key}={value}")
        if row["proposal_id"] != _proposal_id(str(row["proposal_type"]), str(row["source_pointer"])):
            raise ValueError("experiment proposal proposal_id is not deterministic")
        seed = row.get("deterministic_toy_seed")
        if isinstance(seed, bool) or not isinstance(seed, int) or seed < 0:
            raise ValueError("experiment proposal deterministic_toy_seed must be a stable non-negative integer")
        if seed != _toy_seed(str(row["proposal_type"]), str(row["source_pointer"])):
            raise ValueError("experiment proposal deterministic_toy_seed mismatch")
        _non_empty_string_list(row.get("expected_failure_modes"), field="expected_failure_modes")
        _non_empty_string_list(row.get("required_controls"), field="required_controls")
        _non_empty_string_list(row.get("not_claimed"), field="not_claimed")
        draft = row.get("claim_capsule_draft")
        if not isinstance(draft, Mapping):
            raise ValueError("experiment proposal claim_capsule_draft must be an object")
        validated = dict(row)
        validated["claim_capsule_draft"] = _validate_draft(root, draft)
        validated_rows.append(validated)
    proposal_ids = [row["proposal_id"] for row in validated_rows]
    if len(proposal_ids) != len(set(proposal_ids)):
        raise ValueError("experiment proposal proposal_id values must be unique")
    expected_order = sorted(
        validated_rows,
        key=lambda item: (
            SOURCE_CLASS_ORDER.get(str(item["proposal_type"]), 99),
            str(item["source_pointer"]),
            str(item["proposal_type"]),
        ),
    )
    if validated_rows != expected_order:
        raise ValueError("experiment proposal rows are not sorted")
    row_count = payload.get("row_count")
    if isinstance(row_count, bool) or row_count != len(validated_rows):
        raise ValueError("experiment proposal row_count mismatch")
    audit = payload.get("audit")
    if not isinstance(audit, Mapping) or audit.get("status") != "pass":
        raise ValueError("experiment proposal audit must pass")
    result = dict(payload)
    result["rows"] = validated_rows
    return result


def render_experiment_proposals_markdown(payload: Mapping[str, Any]) -> str:
    rows = payload.get("rows")
    row_count = len(rows) if isinstance(rows, list) else 0
    lines = [
        "# Experiment Proposals",
        "",
        f"- Status: `{payload.get('audit', {}).get('status', '')}`",
        f"- Canonical role: `{payload.get('canonical_role', '')}`",
        f"- JSON: `{JSON_ARTIFACT}`",
        f"- Rows: `{row_count}`",
        f"- Source artifacts: `{JSON_ARTIFACT}:$.source_artifacts`",
        "",
        "| proposal | type | source | gap | seed |",
        "| --- | --- | --- | --- | --- |",
    ]
    if isinstance(rows, list):
        for row in rows:
            if not isinstance(row, Mapping):
                continue
            lines.append(
                "| "
                f"`{row.get('proposal_id', '')}` | "
                f"`{row.get('proposal_type', '')}` | "
                f"`{row.get('source_pointer', '')}` | "
                f"`{row.get('source_gap_pointer', '')}` | "
                f"`{row.get('deterministic_toy_seed', '')}` |"
            )
    lines.append("")
    return "\n".join(lines)


def write_experiment_proposals(root: Path, generated_at: str | None = None) -> dict[str, Any]:
    payload = build_experiment_proposals(root, generated_at=generated_at)
    _write_json_atomic(root / JSON_ARTIFACT, payload)
    _write_text_atomic(root / MARKDOWN_ARTIFACT, render_experiment_proposals_markdown(payload))
    return payload
