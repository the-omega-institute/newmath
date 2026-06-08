"""Pointer-only discovery map schema."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import (
    is_resolvable_artifact_pointer,
    resolve_artifact_pointer,
    split_artifact_pointer,
)
from bedc_quality_lab.discovery_compiler.anti_triviality import (
    ANTI_TRIVIALITY_FAMILIES,
    ANTI_TRIVIALITY_POLICY,
)


DISCOVERY_MAP_SCHEMA_ID = "bedc-quality-lab:canonical-discovery-map"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_MARKDOWN_ARTIFACT = "reports/canonical/discovery_map.md"
DISCOVERY_MAP_ARTIFACT_ID = "bedc-quality-lab:discovery-map"
DISCOVERY_LEVELS = ("D0", "D1", "D2", "D3", "D4", "D5-O", "D5-M", "DN", "DR")
POSITIVE_DISCOVERY_LEVELS = frozenset({"D4", "D5-O", "D5-M"})
POSITIVE_DISCOVERY_LEVEL_RANK = {"D4": 0, "D5-O": 1, "D5-M": 2}
COVERAGE_HARDGATE_IDS = (
    "COV-HG1-owner",
    "COV-HG2-resolves",
    "COV-HG3-pointer-only",
    "COV-HG4-positive-support",
    "COV-HG5-dn-witness",
    "COV-HG6-complete-set",
)
COVERAGE_POINTER_FIELDS = (
    "canonical_owner_pointer",
    "discovery_level_pointer",
    "claim_verdict_pointer",
    "mechanism_certificate_pointer",
    "debt_pointer",
    "negative_witness_pointer",
)
COVERAGE_CELL_FIELDS = frozenset(
    {
        "component_id",
        *COVERAGE_POINTER_FIELDS,
        "hardgate_status",
        "hardgate_reason",
    }
)
COVERAGE_FORBIDDEN_KEYS = frozenset(
    {
        "terminal_verdict",
        "terminal_verdicts",
        "metrics",
        "metric",
        "candidate_rows",
        "candidate_row",
        "classifier_reasons",
        "classifier_reason",
        "raw_body",
        "raw_report_body",
        "raw_metrics",
        "copied_evidence",
        "evidence_payload",
        "models",
        "surfaces",
        "model_id",
        "surface_id",
    }
)
REPORTING_VERDICT_FORBIDDEN_KEYS = frozenset(
    {
        "reporting_hardgate",
        "promotion_eligible",
        "claim_capsule_pointer",
        "cost_protocol_pointer",
        "not_claimed_pointer",
    }
)
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
        "anti_triviality_policy",
        "anti_triviality_recommended_level",
        "anti_triviality_failed_gate",
        "anti_triviality_gate_evidence",
        "downgrade_reason",
        "effective_level",
        "hypothesis",
        "next_hypothesis",
        "stop_reason",
        "not_claimed",
        "what_was_learned",
        "bedc_gap_mapping",
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
    def from_mapping(cls, row: Mapping[str, Any], *, root: Path | None = None) -> "DiscoveryMapRow":
        copied_reporting = sorted(key for key in REPORTING_VERDICT_FORBIDDEN_KEYS if key in row)
        if copied_reporting:
            raise ValueError(f"discovery map row copies reporting verdict fields: {', '.join(copied_reporting)}")
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
        if level in POSITIVE_DISCOVERY_LEVELS and root is not None and str(row["audit_status"]) == "valid":
            _validate_positive_row_anti_triviality(root, row)
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


def validate_rows(rows: Sequence[Mapping[str, Any]], *, root: Path | None = None) -> list[DiscoveryMapRow]:
    return [DiscoveryMapRow.from_mapping(row, root=root) for row in rows]


def owner_anti_triviality_check(root: Path, owner_pointer: str, *, accepted_level: str | None = None) -> tuple[bool, str]:
    owner = resolve_artifact_pointer(root, owner_pointer)
    split = split_artifact_pointer(owner_pointer)
    if split is None:
        return False, "anti-triviality-owner-pointer-unresolved"
    artifact, _pointer = split
    if isinstance(owner, Mapping) and _owner_anti_triviality_passes(root, artifact, owner, accepted_level=accepted_level):
        return True, ""
    parent = _artifact_pointer_parent(root, owner_pointer)
    if isinstance(parent, Mapping) and _owner_anti_triviality_passes(root, artifact, parent, accepted_level=accepted_level):
        return True, ""
    artifact_owner = resolve_artifact_pointer(root, f"{artifact}:$")
    if isinstance(artifact_owner, Mapping) and _owner_anti_triviality_passes(
        root,
        artifact,
        artifact_owner,
        accepted_level=accepted_level,
    ):
        return True, ""
    return False, "anti-triviality-owner-contract-not-pass"


def _artifact_pointer_parent(root: Path, owner_pointer: str) -> Any:
    split = split_artifact_pointer(owner_pointer)
    if split is None:
        return None
    artifact, pointer = split
    if pointer == "$" or not pointer.startswith("$."):
        return None
    parent_pointer, _sep, _leaf = pointer.rpartition(".")
    if parent_pointer == "$":
        return resolve_artifact_pointer(root, f"{artifact}:$")
    if not parent_pointer.startswith("$."):
        return None
    return resolve_artifact_pointer(root, f"{artifact}:{parent_pointer}")


def _validate_positive_row_anti_triviality(root: Path, row: Mapping[str, Any]) -> None:
    artifact = row.get("json_artifact")
    evidence = row.get("evidence_pointer")
    if not isinstance(artifact, str) or not artifact:
        raise ValueError("positive discovery map row requires json_artifact")
    if not isinstance(evidence, str) or not evidence.startswith("$."):
        raise ValueError("positive discovery map row requires owner-local evidence_pointer")
    owner_pointer = f"{artifact}:{evidence}"
    ok, reason = owner_anti_triviality_check(root, owner_pointer, accepted_level=str(row.get("discovery_level")))
    if not ok:
        raise ValueError(f"positive discovery map row lacks owner anti-triviality support: {reason}")


def _owner_anti_triviality_passes(
    root: Path,
    artifact: str,
    owner: Mapping[str, Any],
    *,
    accepted_level: str | None = None,
) -> bool:
    status = owner.get("anti_triviality_status")
    evidence = owner.get("anti_triviality_gate_evidence")
    recommended = owner.get("anti_triviality_recommended_level")
    policy = owner.get("anti_triviality_policy")
    if status not in {"pass", "anti_triviality_passed"} or recommended not in POSITIVE_DISCOVERY_LEVELS:
        return False
    if accepted_level in POSITIVE_DISCOVERY_LEVELS:
        if POSITIVE_DISCOVERY_LEVEL_RANK[str(recommended)] < POSITIVE_DISCOVERY_LEVEL_RANK[accepted_level]:
            return False
    if policy != ANTI_TRIVIALITY_POLICY:
        return False
    if not isinstance(evidence, Mapping) or set(evidence) != ANTI_TRIVIALITY_FAMILIES:
        return False
    for family in ANTI_TRIVIALITY_FAMILIES:
        row = evidence.get(family)
        if not isinstance(row, Mapping) or row.get("status") != "pass":
            return False
        pointer = row.get("pointer")
        if not isinstance(pointer, str):
            return False
        qualified = pointer if ":$" in pointer else f"{artifact}:{pointer}"
        if resolve_artifact_pointer(root, qualified) is None:
            return False
    return True

def _optional_string(row: Mapping[str, Any], key: str) -> str | None:
    value = row.get(key)
    if value is None:
        return None
    return str(value)


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


def _pointer_resolves(pointer: Any, *, root: Path | None) -> bool:
    if not isinstance(pointer, str) or split_artifact_pointer(pointer) is None:
        return False
    if pointer.startswith("reports/canonical/discovery_map.json:"):
        return True
    return root is None or is_resolvable_artifact_pointer(root, pointer)


def _validate_coverage_cell(
    cell: Mapping[str, Any],
    *,
    root: Path | None,
) -> dict[str, Any]:
    keys = set(cell)
    if keys != COVERAGE_CELL_FIELDS:
        missing = sorted(COVERAGE_CELL_FIELDS - keys)
        extra = sorted(keys - COVERAGE_CELL_FIELDS)
        detail = []
        if missing:
            detail.append(f"missing {', '.join(missing)}")
        if extra:
            detail.append(f"extra {', '.join(extra)}")
        raise ValueError(f"coverage_matrix cell schema mismatch: {'; '.join(detail)}")
    component_id = cell.get("component_id")
    if not isinstance(component_id, str) or not component_id:
        raise ValueError("coverage_matrix component_id must be a non-empty string")
    if cell.get("hardgate_status") not in {"pass", "fail"}:
        raise ValueError("coverage_matrix cell hardgate_status must be pass or fail")
    if not isinstance(cell.get("hardgate_reason"), str):
        raise ValueError("coverage_matrix cell hardgate_reason must be a string")
    for field in COVERAGE_POINTER_FIELDS:
        pointer = cell.get(field)
        if pointer is not None:
            _validate_artifact_pointer(pointer, field=field)
    payload = dict(cell)
    return payload


def _coverage_gate_statuses(
    cells: Sequence[Mapping[str, Any]],
    *,
    root: Path | None,
    copied: Sequence[str],
    expected_component_ids: frozenset[str] | None,
) -> dict[str, str]:
    observed = {cell.get("component_id") for cell in cells}
    non_dn_cells = [cell for cell in cells if isinstance(cell.get("component_id"), str) and not str(cell["component_id"]).endswith("-DN")]
    dn_cells = [cell for cell in cells if isinstance(cell.get("component_id"), str) and str(cell["component_id"]).endswith("-DN")]
    statuses = {
        "COV-HG1-owner": "pass"
        if all(_pointer_resolves(cell.get("canonical_owner_pointer"), root=root) for cell in cells)
        else "fail",
        "COV-HG2-resolves": "pass"
        if all(_pointer_resolves(cell.get(field), root=root) for cell in cells for field in COVERAGE_POINTER_FIELDS if cell.get(field) is not None)
        else "fail",
        "COV-HG3-pointer-only": "pass" if not copied else "fail",
        "COV-HG4-positive-support": "pass"
        if all(cell.get("mechanism_certificate_pointer") is not None or cell.get("debt_pointer") is not None for cell in non_dn_cells)
        else "fail",
        "COV-HG5-dn-witness": "pass"
        if all(cell.get("negative_witness_pointer") is not None for cell in dn_cells)
        else "fail",
        "COV-HG6-complete-set": "pass" if expected_component_ids is None or observed == expected_component_ids else "fail",
    }
    return statuses


def validate_coverage_matrix(
    coverage_matrix: Mapping[str, Any],
    *,
    rows: Sequence[Mapping[str, Any]] | None = None,
    root: Path | None = None,
    expected_component_ids: frozenset[str] | None = None,
) -> dict[str, Any]:
    del rows
    if coverage_matrix.get("status") not in {"pointer-only", "fail-closed"}:
        raise ValueError("coverage_matrix status must be pointer-only or fail-closed")
    top_keys = set(coverage_matrix)
    expected_top_keys = {"status", "hardgates", "cells"}
    if top_keys != expected_top_keys:
        missing = sorted(expected_top_keys - top_keys)
        extra = sorted(top_keys - expected_top_keys)
        detail = []
        if missing:
            detail.append(f"missing {', '.join(missing)}")
        if extra:
            detail.append(f"extra {', '.join(extra)}")
        raise ValueError(f"coverage_matrix top-level schema mismatch: {'; '.join(detail)}")
    copied = _recursive_forbidden_keys(coverage_matrix, COVERAGE_FORBIDDEN_KEYS)
    if copied:
        raise ValueError(f"coverage_matrix copies owner facts: {', '.join(copied)}")
    cells = coverage_matrix.get("cells")
    if not isinstance(cells, list):
        raise ValueError("coverage_matrix cells must be a list")
    hardgates = coverage_matrix.get("hardgates")
    if not isinstance(hardgates, Mapping):
        raise ValueError("coverage_matrix hardgates must be an object")
    if set(hardgates) != set(COVERAGE_HARDGATE_IDS):
        raise ValueError("coverage_matrix hardgate set mismatch")
    validated_hardgates: dict[str, dict[str, str]] = {}
    for gate_id in COVERAGE_HARDGATE_IDS:
        gate = hardgates.get(gate_id)
        if not isinstance(gate, Mapping):
            raise ValueError("coverage_matrix hardgate entries must be objects")
        if gate.get("status") not in {"pass", "fail"}:
            raise ValueError("coverage_matrix hardgate status must be pass or fail")
        if not isinstance(gate.get("reason"), str):
            raise ValueError("coverage_matrix hardgate reason must be a string")
        validated_hardgates[gate_id] = {"status": str(gate["status"]), "reason": str(gate["reason"])}
    payload = dict(coverage_matrix)
    payload["cells"] = [
        _validate_coverage_cell(cell, root=root)
        if isinstance(cell, Mapping)
        else (_raise_coverage_cell_type())
        for cell in cells
    ]
    observed = {cell["component_id"] for cell in payload["cells"]}
    if expected_component_ids is not None and observed != expected_component_ids:
        missing = sorted(expected_component_ids - observed)
        extra = sorted(observed - expected_component_ids)
        detail = []
        if missing:
            detail.append(f"missing {', '.join(missing)}")
        if extra:
            detail.append(f"extra {', '.join(extra)}")
        raise ValueError(f"coverage_matrix component set mismatch: {'; '.join(detail)}")
    expected_gate_statuses = _coverage_gate_statuses(
        payload["cells"],
        root=root,
        copied=(),
        expected_component_ids=expected_component_ids,
    )
    for gate_id, status in expected_gate_statuses.items():
        if validated_hardgates[gate_id]["status"] != status:
            raise ValueError(f"coverage_matrix {gate_id} status mismatch")
    expected_status = "fail-closed" if any(gate["status"] == "fail" for gate in validated_hardgates.values()) else "pointer-only"
    if coverage_matrix.get("status") != expected_status:
        raise ValueError("coverage_matrix status does not match hardgates")
    return payload


def _raise_coverage_cell_type() -> dict[str, Any]:
    raise ValueError("coverage_matrix cells must be objects")


def validate_discovery_map_payload(payload: Mapping[str, Any], *, root: Path | None = None) -> dict[str, Any]:
    rows = payload.get("rows")
    if not isinstance(rows, list):
        raise ValueError("discovery map rows must be a list")
    validated = [row.as_dict() for row in validate_rows(rows, root=root)]
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
    expected_coverage_component_ids: frozenset[str] | None = None,
) -> dict[str, Any]:
    validated = [row.as_dict() for row in validate_rows(rows, root=root)]
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
        payload["coverage_matrix"] = validate_coverage_matrix(
            coverage_matrix,
            rows=validated,
            root=root,
            expected_component_ids=expected_coverage_component_ids,
        )
    return payload
