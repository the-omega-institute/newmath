"""Pointer-only discovery map schema."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence


DISCOVERY_MAP_SCHEMA_ID = "bedc-quality-lab:canonical-discovery-map"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_MARKDOWN_ARTIFACT = "reports/canonical/discovery_map.md"
DISCOVERY_MAP_ARTIFACT_ID = "bedc-quality-lab:discovery-map"
DISCOVERY_LEVELS = ("D0", "D1", "D2", "D3", "D4", "D5", "D5-O", "DN", "DR")
DN_FACT_KEYS = frozenset(
    {
        "terminal_verdict",
        "classifier_reasons",
        "failed_gate",
        "debt_row_pointer",
        "anti_triviality_status",
        "downgrade_reason",
        "effective_level",
        "hypothesis",
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


def build_discovery_map_payload(
    *,
    rows: Sequence[Mapping[str, Any]],
    generated_at: str,
    manifest_audit: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    validated = [row.as_dict() for row in validate_rows(rows)]
    return {
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
