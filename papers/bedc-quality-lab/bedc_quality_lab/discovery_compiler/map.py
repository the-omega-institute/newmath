"""Pointer-only discovery map schema."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import is_resolvable_artifact_pointer, split_artifact_pointer


DISCOVERY_MAP_SCHEMA_ID = "bedc-quality-lab:canonical-discovery-map"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_MARKDOWN_ARTIFACT = "reports/canonical/discovery_map.md"
DISCOVERY_MAP_ARTIFACT_ID = "bedc-quality-lab:discovery-map"
DISCOVERY_LEVELS = ("D0", "D1", "D2", "D3", "D4", "D5-O", "D5-M", "DN", "DR")
DN_FACT_KEYS = frozenset(
    {
        "report_id",
        "claim_id",
        "terminal_verdict",
        "classifier_reasons",
        "failed_gate",
        "debt_row_pointer",
        "base_level",
        "anti_triviality_status",
        "downgrade_reason",
        "effective_level",
        "hypothesis",
        "next_hypothesis",
        "stop_reason",
        "not_claimed",
        "what_was_learned",
    }
)


@dataclass(frozen=True)
class DiscoveryMapRow:
    report: str
    json_artifact: str
    markdown_artifact: str
    discovery_level: str
    projection_status: str
    evidence_pointer: str | None
    audit_status: str
    audit_reason: str
    negative_report_pointer: str | None
    cells: Mapping[str, Any]

    @classmethod
    def from_mapping(cls, row: Mapping[str, Any]) -> "DiscoveryMapRow":
        required = (
            "report",
            "json_artifact",
            "markdown_artifact",
            "discovery_level",
            "projection_status",
            "audit_status",
            "audit_reason",
        )
        missing = [key for key in required if key not in row]
        if missing:
            raise ValueError(f"discovery map row missing required cells: {', '.join(missing)}")
        level = str(row["discovery_level"])
        if level not in DISCOVERY_LEVELS:
            raise ValueError(f"unsupported discovery level: {level}")
        if level == "DN":
            copied = sorted(key for key in DN_FACT_KEYS if key in row)
            if copied:
                raise ValueError(f"DN discovery map row copies owner facts: {', '.join(copied)}")
            negative_pointer = row.get("negative_report_pointer")
            if not isinstance(negative_pointer, str) or not negative_pointer.startswith("reports/canonical/negative_discovery_reports.json:$."):
                raise ValueError("DN discovery map row must point to negative_discovery_reports")
        else:
            negative_pointer = row.get("negative_report_pointer")
            if negative_pointer is not None:
                raise ValueError("non-DN discovery map row must not carry negative_report_pointer")
        evidence = row.get("evidence_pointer")
        if evidence is not None and not isinstance(evidence, str):
            raise ValueError("evidence_pointer must be a string or null")
        return cls(
            report=str(row["report"]),
            json_artifact=str(row["json_artifact"]),
            markdown_artifact=str(row["markdown_artifact"]),
            discovery_level=level,
            projection_status=str(row["projection_status"]),
            evidence_pointer=evidence,
            audit_status=str(row["audit_status"]),
            audit_reason=str(row["audit_reason"]),
            negative_report_pointer=negative_pointer,
            cells=row,
        )

    def as_dict(self) -> dict[str, Any]:
        return dict(self.cells)


def level_counts(rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {level: sum(1 for row in rows if row.get("discovery_level") == level) for level in DISCOVERY_LEVELS}


def validate_rows(rows: Sequence[Mapping[str, Any]]) -> list[DiscoveryMapRow]:
    return [DiscoveryMapRow.from_mapping(row) for row in rows]


def _recursive_forbidden_keys(payload: Any, forbidden: frozenset[str], *, path: tuple[str, ...] = ()) -> list[str]:
    found: set[str] = set()
    if isinstance(payload, Mapping):
        for key, value in payload.items():
            key_text = str(key)
            child_path = path + (key_text,)
            if key_text in forbidden or child_path[-2:] == ("host", "env"):
                found.add(".".join(child_path))
            found.update(_recursive_forbidden_keys(value, forbidden, path=child_path))
    elif isinstance(payload, list):
        for index, value in enumerate(payload):
            found.update(_recursive_forbidden_keys(value, forbidden, path=path + (f"[{index}]",)))
    return sorted(found)


def _validate_artifact_pointer(pointer: Any, *, field: str = "owner_pointer") -> str:
    if not isinstance(pointer, str):
        raise ValueError(f"coverage_matrix {field} must be a string")
    split = split_artifact_pointer(pointer)
    if split is None:
        raise ValueError(f"coverage_matrix {field} must be artifact-qualified")
    return pointer


def _validate_negative_owner_pointer(pointer: Any) -> str:
    pointer = _validate_artifact_pointer(pointer)
    split = split_artifact_pointer(pointer)
    assert split is not None
    artifact, local_pointer = split
    if artifact == "reports/canonical/negative_discovery_reports.json":
        if not local_pointer.startswith("$.rows["):
            raise ValueError("coverage_matrix negative_owner_pointer must point to a negative owner row")
        return pointer
    if artifact.startswith("reports/runs/") and ".negative_witness[" in local_pointer:
        return pointer
    if artifact.startswith("reports/runs/") and ".negative_witness." in local_pointer:
        return pointer
    raise ValueError("coverage_matrix negative_owner_pointer must point to a negative owner row or run-local negative witness")


def _discovery_targets(rows: Sequence[Mapping[str, Any]]) -> dict[str, Mapping[str, Any]]:
    targets: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        target = row.get("report")
        if not isinstance(target, str) or not target:
            raise ValueError("discovery map row report must be a non-empty string")
        if target in targets:
            raise ValueError(f"duplicate discovery target: {target}")
        targets[target] = row
    return targets


def _coverage_matrix_overall_state(cells: Sequence[Mapping[str, Any]]) -> str:
    return (
        "present-but-fail-closed"
        if any(cell.get("slot_state") == "present-but-fail-closed" for cell in cells)
        else "present"
    )


def _validate_coverage_cell(
    cell: Mapping[str, Any],
    *,
    rows_by_target: Mapping[str, Mapping[str, Any]] | None,
    root: Path | None,
) -> dict[str, Any]:
    expected_keys = {"target", "owner_pointer", "slot_state"}
    keys = set(cell)
    if keys != expected_keys:
        missing = sorted(expected_keys - keys)
        extra = sorted(keys - expected_keys)
        detail = []
        if missing:
            detail.append(f"missing {', '.join(missing)}")
        if extra:
            detail.append(f"extra {', '.join(extra)}")
        raise ValueError(f"coverage_matrix cell schema mismatch: {'; '.join(detail)}")
    copied = _recursive_forbidden_keys(cell, frozenset({"terminal_verdict", "metrics"}))
    if copied:
        raise ValueError(f"coverage_matrix cell copies owner facts: {', '.join(copied)}")
    target = cell.get("target")
    if not isinstance(target, str) or not target:
        raise ValueError("coverage_matrix cell target must be a non-empty string")
    owner_pointer = _validate_artifact_pointer(cell.get("owner_pointer"))
    slot_state = cell.get("slot_state")
    if slot_state not in {"present", "present-but-fail-closed", "negative"}:
        raise ValueError("coverage_matrix cell slot_state must be present, present-but-fail-closed, or negative")
    if rows_by_target is not None:
        row = rows_by_target.get(target)
        if row is None:
            raise ValueError(f"coverage_matrix cell target is not a discovery row: {target}")
        if row.get("discovery_level") == "DN":
            if slot_state != "negative":
                raise ValueError(f"DN coverage_matrix cell must be negative: {target}")
            if owner_pointer != row.get("negative_report_pointer"):
                raise ValueError(f"DN coverage_matrix cell owner pointer mismatch: {target}")
            _validate_negative_owner_pointer(owner_pointer)
        elif slot_state == "negative":
            raise ValueError(f"non-DN coverage_matrix cell must not be negative: {target}")
    if root is not None:
        resolved = is_resolvable_artifact_pointer(root, owner_pointer)
        if slot_state in {"present", "negative"} and not resolved:
            raise ValueError(f"coverage_matrix owner pointer does not resolve: {target}")
        if slot_state == "present-but-fail-closed" and resolved:
            raise ValueError(f"coverage_matrix fail-closed pointer unexpectedly resolves: {target}")
    payload = dict(cell)
    return payload


def validate_coverage_matrix(
    coverage_matrix: Mapping[str, Any],
    *,
    rows: Sequence[Mapping[str, Any]] | None = None,
    root: Path | None = None,
) -> dict[str, Any]:
    if coverage_matrix.get("status") != "pointer-only":
        raise ValueError("coverage_matrix status must be pointer-only")
    copied = _recursive_forbidden_keys(coverage_matrix, frozenset({"terminal_verdict", "metrics"}))
    if copied:
        raise ValueError(f"coverage_matrix copies owner facts: {', '.join(copied)}")
    cells = coverage_matrix.get("cells")
    if not isinstance(cells, list):
        raise ValueError("coverage_matrix cells must be a list")
    rows_by_target = _discovery_targets(rows) if rows is not None else None
    payload = dict(coverage_matrix)
    payload["cells"] = [
        _validate_coverage_cell(cell, rows_by_target=rows_by_target, root=root)
        if isinstance(cell, Mapping)
        else (_raise_coverage_cell_type())
        for cell in cells
    ]
    if rows_by_target is not None:
        observed = {cell["target"] for cell in payload["cells"]}
        expected = set(rows_by_target)
        if observed != expected:
            missing = sorted(expected - observed)
            extra = sorted(observed - expected)
            detail = []
            if missing:
                detail.append(f"missing {', '.join(missing)}")
            if extra:
                detail.append(f"extra {', '.join(extra)}")
            raise ValueError(f"coverage_matrix target set mismatch: {'; '.join(detail)}")
    expected_state = _coverage_matrix_overall_state(payload["cells"])
    if coverage_matrix.get("overall_state") != expected_state:
        raise ValueError("coverage_matrix overall_state does not match cell slot states")
    return payload


def _raise_coverage_cell_type() -> dict[str, Any]:
    raise ValueError("coverage_matrix cells must be objects")


def validate_discovery_map_payload(payload: Mapping[str, Any], *, root: Path | None = None) -> dict[str, Any]:
    rows = payload.get("rows")
    if not isinstance(rows, list):
        raise ValueError("discovery map rows must be a list")
    validated = [row.as_dict() for row in validate_rows(rows)]
    coverage_matrix = payload.get("coverage_matrix")
    if coverage_matrix is not None:
        if not isinstance(coverage_matrix, Mapping):
            raise ValueError("discovery map coverage_matrix must be an object")
        validate_coverage_matrix(coverage_matrix, rows=validated, root=root)
    return dict(payload)


def build_discovery_map_payload(
    *,
    rows: Sequence[Mapping[str, Any]],
    generated_at: str,
    manifest_audit: Mapping[str, Any] | None = None,
    coverage_matrix: Mapping[str, Any] | None = None,
    root: Path | None = None,
) -> dict[str, Any]:
    validated = [row.as_dict() for row in validate_rows(rows)]
    payload = {
        "schema_id": DISCOVERY_MAP_SCHEMA_ID,
        "artifact_id": DISCOVERY_MAP_ARTIFACT_ID,
        "generated_at": generated_at,
        "json_artifact": DISCOVERY_MAP_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_MAP_MARKDOWN_ARTIFACT,
        "row_count": len(validated),
        "level_counts": level_counts(validated),
        "manifest_audit": dict(manifest_audit or {"unregistered_json_artifacts": []}),
        "rows": validated,
    }
    if coverage_matrix is not None:
        payload["coverage_matrix"] = validate_coverage_matrix(coverage_matrix, rows=validated, root=root)
    return payload
