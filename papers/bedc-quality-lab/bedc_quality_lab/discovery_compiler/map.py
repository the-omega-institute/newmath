"""Pointer-only discovery map schema."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import split_artifact_pointer


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


def _recursive_forbidden_keys(payload: Any, forbidden: frozenset[str]) -> list[str]:
    found: set[str] = set()
    if isinstance(payload, Mapping):
        found.update(str(key) for key in payload if key in forbidden)
        for value in payload.values():
            found.update(_recursive_forbidden_keys(value, forbidden))
    elif isinstance(payload, list):
        for value in payload:
            found.update(_recursive_forbidden_keys(value, forbidden))
    return sorted(found)


def _validate_negative_owner_pointer(pointer: Any) -> str | None:
    if pointer is None:
        return None
    if not isinstance(pointer, str):
        raise ValueError("coverage_matrix negative_owner_pointer must be a string or null")
    split = split_artifact_pointer(pointer)
    if split is None:
        raise ValueError("coverage_matrix negative_owner_pointer must be artifact-qualified")
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


def _validate_coverage_cell(cell: Mapping[str, Any]) -> dict[str, Any]:
    required = (
        "model_id",
        "surface_id",
        "coverage_level",
        "pointer_status",
        "source_artifact",
        "status_pointer",
        "evidence_pointer",
        "hardgate_pointer",
        "discovery_map_row_pointer",
    )
    missing = [key for key in required if key not in cell]
    if missing:
        raise ValueError(f"coverage_matrix cell missing required keys: {', '.join(missing)}")
    copied = _recursive_forbidden_keys(cell, DN_FACT_KEYS | {"terminal_verdict"})
    if copied:
        raise ValueError(f"coverage_matrix cell copies owner facts: {', '.join(copied)}")
    for key in ("model_id", "surface_id", "coverage_level", "pointer_status", "source_artifact", "status_pointer", "evidence_pointer"):
        if not isinstance(cell.get(key), str):
            raise ValueError(f"coverage_matrix cell {key} must be a string")
    for key in ("hardgate_pointer", "discovery_map_row_pointer"):
        if cell.get(key) is not None and not isinstance(cell.get(key), str):
            raise ValueError(f"coverage_matrix cell {key} must be a string or null")
    if str(cell["pointer_status"]) not in {"resolved", "unresolved"}:
        raise ValueError("coverage_matrix cell pointer_status must be resolved or unresolved")
    payload = dict(cell)
    if "negative_owner_pointer" in payload:
        payload["negative_owner_pointer"] = _validate_negative_owner_pointer(payload["negative_owner_pointer"])
    return payload


def validate_coverage_matrix(coverage_matrix: Mapping[str, Any]) -> dict[str, Any]:
    if coverage_matrix.get("status") != "pointer-only":
        raise ValueError("coverage_matrix status must be pointer-only")
    copied = _recursive_forbidden_keys(coverage_matrix, DN_FACT_KEYS | {"terminal_verdict"})
    if copied:
        raise ValueError(f"coverage_matrix copies owner facts: {', '.join(copied)}")
    cells = coverage_matrix.get("cells")
    models = coverage_matrix.get("models")
    surfaces = coverage_matrix.get("surfaces")
    if not isinstance(cells, list):
        raise ValueError("coverage_matrix cells must be a list")
    if not isinstance(models, list):
        raise ValueError("coverage_matrix models must be a list")
    if not isinstance(surfaces, list):
        raise ValueError("coverage_matrix surfaces must be a list")
    payload = dict(coverage_matrix)
    payload["cells"] = [
        _validate_coverage_cell(cell)
        if isinstance(cell, Mapping)
        else (_raise_coverage_cell_type())
        for cell in cells
    ]
    return payload


def _raise_coverage_cell_type() -> dict[str, Any]:
    raise ValueError("coverage_matrix cells must be objects")


def build_discovery_map_payload(
    *,
    rows: Sequence[Mapping[str, Any]],
    generated_at: str,
    manifest_audit: Mapping[str, Any] | None = None,
    coverage_matrix: Mapping[str, Any] | None = None,
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
        payload["coverage_matrix"] = validate_coverage_matrix(coverage_matrix)
    return payload
