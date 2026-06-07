"""Generic projection helpers for backend-supplied discovery rows."""

from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .map import DISCOVERY_MAP_JSON_ARTIFACT, DISCOVERY_MAP_MARKDOWN_ARTIFACT, build_discovery_map_payload
from .pointers import normalize_artifact_pointer, pointer_value, resolve_artifact_pointer


POSITIVE_DISCOVERY_LEVELS = frozenset({"D0", "D1", "D2", "D3", "D4", "D5-O", "D5-M"})
FINITE_GATE_NOT_CLAIMED = (
    "finite gate checks finite evidence-set structure, not model-result correctness",
    "finite gate does not own negative witness report facts",
)


def build_discovery_map(
    *,
    rows: Sequence[Mapping[str, Any]],
    generated_at: str | None = None,
    manifest_audit: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    return build_discovery_map_payload(rows=rows, generated_at=timestamp, manifest_audit=manifest_audit)


def _rows(payload: Mapping[str, Any], key: str = "rows") -> list[Mapping[str, Any]]:
    value = payload.get(key)
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        return []
    return [row for row in value if isinstance(row, Mapping)]


def _materialized_rows(payloads: Mapping[str, Any], key: str) -> list[Mapping[str, Any]]:
    value = payloads.get(key)
    if isinstance(value, Mapping):
        return _rows(value)
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return [row for row in value if isinstance(row, Mapping)]
    return []


def _row_pointer(artifact: str, index: int) -> str:
    return f"{artifact}:$.rows[{index}]"


def _evidence_pointer(row: Mapping[str, Any], index: int) -> str:
    artifact = row.get("json_artifact")
    pointer = row.get("evidence_pointer")
    if isinstance(artifact, str) and isinstance(pointer, str) and pointer.startswith("$."):
        return f"{artifact}:{pointer}"
    if isinstance(pointer, str) and ":$." in pointer:
        return pointer
    return _row_pointer(DISCOVERY_MAP_JSON_ARTIFACT, index)


def _string_cell(row: Mapping[str, Any], key: str) -> str | None:
    value = row.get(key)
    return value if isinstance(value, str) and value else None


def _negative_pointer_tuple(row: Mapping[str, Any], index: int) -> list[str]:
    return [
        _string_cell(row, "negative_id") or "",
        _row_pointer("reports/canonical/discovery_negative_witness_summary.json", index),
        _string_cell(row, "discovery_map_pointer") or "",
        _string_cell(row, "witness_pointer") or "",
        _string_cell(row, "claim_verdict_pointer") or "",
    ]


def _revocation_pointer(row: Mapping[str, Any], index: int) -> str:
    for key in ("source_ref", "certificate_source_ref", "source_pointer", "ledger_pointer"):
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return _row_pointer(DISCOVERY_MAP_JSON_ARTIFACT, index)


def _hardgate(status: bool, reason: str) -> dict[str, str]:
    return {"status": "pass" if status else "fail", "reason": reason}


def _artifact_pointer(artifact: Any, pointer: Any) -> str | None:
    if not isinstance(pointer, str) or not pointer:
        return None
    if normalize_artifact_pointer(pointer) is not None:
        return pointer
    if isinstance(artifact, str) and artifact and pointer.startswith("$."):
        return f"{artifact}:{pointer}"
    return None


def _collect_discovery_map_pointer_cells(discovery_map: Mapping[str, Any]) -> list[tuple[str, str]]:
    cells: list[tuple[str, str]] = []
    for index, row in enumerate(_rows(discovery_map)):
        artifact = row.get("json_artifact")
        keys = {
            "evidence_pointer",
            "negative_report_pointer",
            "control_pointer",
            "failed_gate",
            "debt_row_pointer",
            *(key for key in row if key.endswith("_pointer")),
        }
        for key in sorted(keys):
            pointer = _artifact_pointer(artifact, row.get(key))
            if pointer is not None:
                cells.append((f"discovery_map.rows[{index}].{key}", pointer))
    coverage = discovery_map.get("coverage_matrix")
    coverage_cells = coverage.get("cells") if isinstance(coverage, Mapping) else None
    if isinstance(coverage_cells, Sequence) and not isinstance(coverage_cells, (str, bytes, bytearray)):
        for index, cell in enumerate(item for item in coverage_cells if isinstance(item, Mapping)):
            artifact = cell.get("source_artifact")
            keys = {
                "source_pointer",
                "discovery_map_row_pointer",
                *(key for key in cell if key.endswith("_pointer")),
            }
            for key in sorted(keys):
                pointer = _artifact_pointer(artifact, cell.get(key))
                if pointer is not None:
                    cells.append((f"discovery_map.coverage_matrix.cells[{index}].{key}", pointer))
    return cells


def _collect_negative_summary_pointer_cells(negative_summary: Mapping[str, Any]) -> list[tuple[str, str]]:
    cells: list[tuple[str, str]] = []
    for index, row in enumerate(_rows(negative_summary)):
        for key in ("ledger_pointer", "discovery_map_pointer", "witness_pointer", "claim_verdict_pointer"):
            value = row.get(key)
            if isinstance(value, str) and value:
                cells.append((f"negative_witness_summary.rows[{index}].{key}", value))
    return cells


def _collect_revocation_pointer_cells(payloads: Mapping[str, Any]) -> list[tuple[str, str]]:
    cells: list[tuple[str, str]] = []
    for owner, key in (("revocation_ledger", "revocation_ledger"), ("revocations", "revocations")):
        for index, row in enumerate(_materialized_rows(payloads, key)):
            for field in ("source_ref", "certificate_source_ref", "source_pointer", "ledger_pointer"):
                value = row.get(field)
                if isinstance(value, str) and value:
                    cells.append((f"{owner}.rows[{index}].{field}", value))
    return cells


def _jsonl_pointer_value(path: Path, pointer: str) -> Any:
    if not pointer.startswith("$.lines[") or not pointer.endswith("]"):
        return None
    index_text = pointer.removeprefix("$.lines[").removesuffix("]")
    if not index_text.isdigit():
        return None
    rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]
    index = int(index_text)
    return rows[index] if index < len(rows) else None


def _pointer_failure_reason(root: Path, normalized_pointer: str) -> str | None:
    artifact, pointer = normalized_pointer.split(":", 1)
    path = root / artifact
    if not path.exists():
        return "missing-artifact"
    if artifact.endswith(".jsonl"):
        if not pointer.startswith("$.lines[") or not pointer.endswith("]"):
            return "malformed"
        try:
            return None if _jsonl_pointer_value(path, pointer) is not None else "unresolved-pointer"
        except json.JSONDecodeError:
            return "json-decode"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return "json-decode"
    if pointer == "$":
        return None
    if not isinstance(payload, Mapping):
        return "unresolved-pointer"
    return None if pointer_value(payload, pointer) is not None else "unresolved-pointer"


def _stale_pointers(root: Path | None, cells: Sequence[tuple[str, str]]) -> list[dict[str, str]]:
    if root is None:
        return []
    stale: list[dict[str, str]] = []
    for owner, pointer in cells:
        normalized = normalize_artifact_pointer(pointer)
        if normalized is None:
            stale.append(
                {
                    "pointer": pointer,
                    "normalized_pointer": "",
                    "owner": owner,
                    "reason": "malformed",
                }
            )
            continue
        reason = _pointer_failure_reason(root, normalized)
        if reason is not None or resolve_artifact_pointer(root, normalized) is None:
            stale.append(
                {
                    "pointer": pointer,
                    "normalized_pointer": normalized,
                    "owner": owner,
                    "reason": reason or "unresolved-pointer",
                }
            )
    return sorted(stale, key=lambda item: (item["owner"], item["pointer"], item["normalized_pointer"]))


def project_finite_discovery_gate(payloads: Mapping[str, Any], *, root: Path | None = None) -> dict[str, Any]:
    discovery_map = payloads.get("discovery_map")
    map_rows = _rows(discovery_map) if isinstance(discovery_map, Mapping) else []
    negative_summary = payloads.get("negative_witness_summary")
    negative_rows = _rows(negative_summary) if isinstance(negative_summary, Mapping) else []
    ledger_rows = _materialized_rows(payloads, "revocation_ledger")
    revocation_rows = _materialized_rows(payloads, "revocations")

    positive_pointers = sorted(
        _evidence_pointer(row, index)
        for index, row in enumerate(map_rows)
        if row.get("discovery_level") in POSITIVE_DISCOVERY_LEVELS
    )
    negative_pointers = sorted(_negative_pointer_tuple(row, index) for index, row in enumerate(negative_rows))
    map_revocation_pointers = [
        _evidence_pointer(row, index)
        for index, row in enumerate(map_rows)
        if row.get("discovery_level") == "DR"
    ]
    ledger_revocation_pointers = [
        _revocation_pointer(row, index) for index, row in enumerate([*ledger_rows, *revocation_rows])
    ]
    revocation_pointers = sorted([*map_revocation_pointers, *ledger_revocation_pointers])

    negative_ids = [_string_cell(row, "negative_id") for row in negative_rows]
    negative_ids = [value for value in negative_ids if value is not None]
    positive_unique = len(set(positive_pointers)) == len(positive_pointers)
    negative_unique = len(set(negative_ids)) == len(negative_ids) == len(negative_rows)
    revocation_unique = len(set(revocation_pointers)) == len(revocation_pointers)

    negative_row_count = negative_summary.get("row_count") if isinstance(negative_summary, Mapping) else None
    negative_audit_pass = not isinstance(negative_summary, Mapping) or negative_summary.get("audit_status") == "pass"
    positive_parity = len(positive_pointers) == sum(
        1 for row in map_rows if row.get("discovery_level") in POSITIVE_DISCOVERY_LEVELS
    )
    negative_parity = negative_row_count == len(negative_rows)
    revocation_parity = len(revocation_pointers) == len(map_revocation_pointers) + len(ledger_revocation_pointers)
    pointer_cells: list[tuple[str, str]] = []
    if isinstance(discovery_map, Mapping):
        pointer_cells.extend(_collect_discovery_map_pointer_cells(discovery_map))
    if isinstance(negative_summary, Mapping):
        pointer_cells.extend(_collect_negative_summary_pointer_cells(negative_summary))
    pointer_cells.extend(_collect_revocation_pointer_cells(payloads))
    stale_pointers = _stale_pointers(root, pointer_cells)
    stale_status = root is not None and not stale_pointers

    positive_set = set(positive_pointers)
    negative_set = {cell for row in negative_pointers for cell in row[1:] if isinstance(cell, str)}
    revocation_set = set(revocation_pointers)
    overlap_pairs = {
        "positive_negative": sorted(positive_set & negative_set),
        "positive_revocation": sorted(positive_set & revocation_set),
        "negative_revocation": sorted(negative_set & revocation_set),
    }
    if overlap_pairs["positive_revocation"]:
        overlap_status = "revocation-positive-overlap"
    elif overlap_pairs["positive_negative"]:
        overlap_status = "positive-negative-overlap"
    elif overlap_pairs["negative_revocation"]:
        overlap_status = "revocation-negative-overlap"
    else:
        overlap_status = "disjoint"

    hardgates = {
        "FG-HG1": _hardgate(positive_parity and positive_unique, "positive evidence pointers are finite and unique"),
        "FG-HG2": _hardgate(negative_parity and negative_unique and negative_audit_pass, "negative summary ids and row pointers are finite"),
        "FG-HG3": _hardgate(revocation_parity and revocation_unique, "revocation pointers are finite with explicit overlap status"),
        "FG-HG4": _hardgate(True, "finite projection is materialized and sorted deterministically"),
        "FG-HG5": _hardgate(stale_status, "finite gate artifact pointers resolve under the report root"),
    }
    failures = sorted(name for name, gate in hardgates.items() if gate["status"] != "pass")
    counts = {
        "positive": len(positive_pointers),
        "positive_pointers": len(positive_pointers),
        "negative": len(negative_rows),
        "negative_pointers": len(negative_pointers),
        "revocation": len(revocation_pointers),
        "revocation_pointers": len(revocation_pointers),
        "discovery_map_rows": len(map_rows),
        "negative_summary_rows": len(negative_rows),
        "negative_summary_report_rows": int(negative_summary.get("dn_discovery_map_row_count", 0))
        if isinstance(negative_summary, Mapping) and type(negative_summary.get("dn_discovery_map_row_count")) is int
        else 0,
        "negative_summary_witness_rows": int(negative_summary.get("witness_row_count", 0))
        if isinstance(negative_summary, Mapping) and type(negative_summary.get("witness_row_count")) is int
        else 0,
        "negative_summary_claim_verdict_rows": int(negative_summary.get("claim_verdict_row_count", 0))
        if isinstance(negative_summary, Mapping) and type(negative_summary.get("claim_verdict_row_count")) is int
        else 0,
    }
    return {
        "status": "pass" if not failures else "fail",
        "hardgates": hardgates,
        "counts": counts,
        "pointers": {
            "positive": positive_pointers,
            "negative": negative_pointers,
            "revocation": revocation_pointers,
        },
        "overlaps": {
            "status": overlap_status,
            **overlap_pairs,
        },
        "stale_pointers": stale_pointers,
        "not_claimed": list(FINITE_GATE_NOT_CLAIMED),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Discovery Map",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Rows: `{payload['row_count']}`",
        "",
        "| report | level | projection | audit | evidence |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        pointer = row.get("negative_report_pointer") or row.get("evidence_pointer") or row["projection_status"]
        lines.append(
            "| "
            f"`{row['report']}` | "
            f"`{row['discovery_level']}` | "
            f"`{row['projection_status']}` | "
            f"`{row['audit_status']}` | "
            f"`{pointer}` |"
        )
    lines.append("")
    return "\n".join(lines)


def write_discovery_map(
    *,
    root: Path,
    rows: Sequence[Mapping[str, Any]],
    generated_at: str | None = None,
    manifest_audit: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    payload = build_discovery_map(rows=rows, generated_at=generated_at, manifest_audit=manifest_audit)
    json_path = root / DISCOVERY_MAP_JSON_ARTIFACT
    markdown_path = root / DISCOVERY_MAP_MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload
