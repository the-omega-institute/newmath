"""Shared projection consistency checks for generated aggregate reports."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import re
from typing import Any, Mapping, Sequence

from bedc_quality_lab.artifact_freshness import load_artifact_snapshot
from bedc_quality_lab.claim_graph import (
    CLAIM_GRAPH_JSON_ARTIFACT,
    CLAIM_VERDICTS_JSONL_ARTIFACT,
    validate_terminal_node_projection,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.claim_graph import resolve_source_pointer


SCHEMA_ID = "bedc-quality-lab:aggregation-consistency"
QUALITY_SCORECARD_ARTIFACT = "reports/canonical/quality-scorecard.json"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
NEGATIVE_WITNESS_SUMMARY_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.json"
INDEX_ARTIFACT = "reports/canonical/index.json"

def _phrase(*parts: str) -> str:
    return "".join(parts)


DOC_HG_FORBIDDEN_PHRASES = (
    _phrase("DGT 已有训练", "实证优于 Transformer"),
    _phrase("L1 scaling ", "成功"),
    _phrase("DGT 泛化到 ", "tiny sequence"),
    _phrase("学会 ", "order-2 rule"),
    _phrase("组件因果", "已全部证明"),
    _phrase("separation", "-persists"),
    _phrase("base_transformer", "_l1"),
)

DOC_HG_DEFAULT_PATHS = (
    "docs/bedc_quality_lab_v1.md",
    "docs/v1_report_outline.md",
    "docs/bedc_quality_lab_alpha_milestone.md",
    "docs/claims_and_nonclaims.md",
    "docs/artifact_manifest.md",
    "reports/canonical/dgt-l1-boundary-report.md",
    "reports/canonical/scaling-ladder.md",
    "reports/canonical/model-comparison.md",
    "reports/canonical/index.md",
    "reports/canonical/experiment_proposals.md",
)

BOUNDARY_POINTER_RE = re.compile(
    r"(?:boundary|scope|not[-_ ]claimed|correction|owner|hardgate|gate)[A-Za-z0-9_\-./:#$\\[\\]]*",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class ProjectionBinding:
    owner_pointer: str
    derived_pointer: str
    projection_kind: str
    field_name: str


@dataclass(frozen=True)
class AggregationConsistencyReport:
    errors: list[str]
    hardgates: dict[str, str]
    binding_count: int
    doc_scan_count: int

    def compact_status(self, *, generated_at: str | None = None) -> dict[str, Any]:
        return {
            "schema_id": SCHEMA_ID,
            "status": "pass" if not self.errors else "fail",
            "hardgate_status": dict(self.hardgates),
            "binding_count": self.binding_count,
            "doc_scan_count": self.doc_scan_count,
            "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        }


def _load_json(root: Path, artifact: str) -> Any:
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def _load_json_object(root: Path, artifact: str) -> Mapping[str, Any] | None:
    path = root / artifact
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload if isinstance(payload, Mapping) else None


def _load_jsonl_rows(root: Path, artifact: str) -> list[dict[str, Any]]:
    path = root / artifact
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        row = json.loads(line)
        if not isinstance(row, dict):
            raise ValueError(f"JSONL row must be an object: {artifact}")
        rows.append(row)
    return rows


def build_projection_bindings(root: Path) -> list[ProjectionBinding]:
    bindings: list[ProjectionBinding] = []
    if (root / INDEX_ARTIFACT).exists():
        bindings.extend(
            [
                ProjectionBinding(
                    f"{QUALITY_SCORECARD_ARTIFACT}:$.rows",
                    f"{INDEX_ARTIFACT}:$.quality_scorecard.metric_count",
                    "count",
                    "metric_count",
                ),
                ProjectionBinding(
                    f"{DISCOVERY_MAP_ARTIFACT}:$.rows",
                    f"{INDEX_ARTIFACT}:$.discovery_map.row_count",
                    "count",
                    "row_count",
                ),
                ProjectionBinding(
                    f"{CLAIM_VERDICTS_JSONL_ARTIFACT}:$",
                    f"{INDEX_ARTIFACT}:$.claim_verdicts.row_count",
                    "jsonl_count",
                    "row_count",
                ),
                ProjectionBinding(
                    f"{CLAIM_GRAPH_JSON_ARTIFACT}:$.node_count",
                    f"{INDEX_ARTIFACT}:$.claim_graph.node_count",
                    "value",
                    "node_count",
                ),
                ProjectionBinding(
                    f"{NEGATIVE_WITNESS_SUMMARY_ARTIFACT}:$.row_count",
                    f"{INDEX_ARTIFACT}:$.negative_witness_summary.row_count",
                    "value",
                    "row_count",
                ),
            ]
        )

    claim_graph = _load_json_object(root, CLAIM_GRAPH_JSON_ARTIFACT) or {}
    nodes = claim_graph.get("nodes")
    if isinstance(nodes, list):
        for index, node in enumerate(nodes):
            if not isinstance(node, Mapping) or node.get("node_type") != "terminal_claim":
                continue
            source_pointer = node.get("source_pointer")
            if isinstance(source_pointer, str):
                bindings.append(
                    ProjectionBinding(
                        source_pointer,
                        f"{CLAIM_GRAPH_JSON_ARTIFACT}:$.nodes[{index}].terminal_verdict",
                        "terminal_verdict",
                        "terminal_verdict",
                    )
                )
    return bindings


def _derived_value(root: Path, binding: ProjectionBinding, payloads: Mapping[str, Any]) -> Any:
    if binding.derived_pointer.startswith(f"{INDEX_ARTIFACT}:") and INDEX_ARTIFACT in payloads:
        pointer = binding.derived_pointer.split(":", 1)[1]
        payload = payloads[INDEX_ARTIFACT]
        return pointer_value(payload, pointer) if isinstance(payload, Mapping) else None
    return resolve_source_pointer(root, binding.derived_pointer)


def _owner_value(root: Path, binding: ProjectionBinding) -> Any:
    if binding.projection_kind == "count":
        value = resolve_source_pointer(root, binding.owner_pointer)
        return len(value) if isinstance(value, list) else None
    if binding.projection_kind == "jsonl_count":
        return len(_load_jsonl_rows(root, CLAIM_VERDICTS_JSONL_ARTIFACT))
    if binding.projection_kind == "pointer":
        return binding.owner_pointer
    if binding.projection_kind == "terminal_verdict":
        value = resolve_source_pointer(root, binding.owner_pointer)
        return value.get("claim_verdict") if isinstance(value, Mapping) else None
    return resolve_source_pointer(root, binding.owner_pointer)


def _validate_bindings(
    root: Path,
    bindings: Sequence[ProjectionBinding],
    payloads: Mapping[str, Any],
) -> tuple[list[str], str]:
    errors: list[str] = []
    for binding in bindings:
        owner = _owner_value(root, binding)
        derived = _derived_value(root, binding, payloads)
        if owner is None:
            errors.append(f"AGG-HG1 owner pointer missing: {binding.owner_pointer}")
            continue
        if derived is None:
            errors.append(f"AGG-HG1 derived pointer missing: {binding.derived_pointer}")
            continue
        if owner != derived:
            errors.append(
                f"AGG-HG1 projection mismatch: {binding.owner_pointer} -> {binding.derived_pointer}"
            )
    return errors, "pass" if not errors else "fail"


def _validate_freshness(root: Path) -> tuple[list[str], str]:
    errors: list[str] = []
    owners = {
        artifact: load_artifact_snapshot(root, artifact)
        for artifact in (
            QUALITY_SCORECARD_ARTIFACT,
            DISCOVERY_MAP_ARTIFACT,
            CLAIM_GRAPH_JSON_ARTIFACT,
            NEGATIVE_WITNESS_SUMMARY_ARTIFACT,
        )
        if (root / artifact).exists()
    }
    index_snapshot = load_artifact_snapshot(root, INDEX_ARTIFACT)
    if not index_snapshot.sha256:
        return ["AGG-HG2 canonical index missing"], "fail"
    for artifact, snapshot in owners.items():
        if snapshot.sha256 and index_snapshot.generated_at and snapshot.generated_at:
            if snapshot.generated_at > index_snapshot.generated_at:
                errors.append(f"AGG-HG2 owner newer than index: {artifact}")
    scorecard_snapshot = load_artifact_snapshot(root, QUALITY_SCORECARD_ARTIFACT)
    if scorecard_snapshot.sha256:
        for index, row in enumerate(_load_jsonl_rows(root, CLAIM_VERDICTS_JSONL_ARTIFACT)):
            row_hash = row.get("scorecard_hash")
            if isinstance(row_hash, str) and row_hash != scorecard_snapshot.sha256:
                errors.append(f"AGG-HG2 scorecard hash mismatch in claim verdict row: {index}")
    return errors, "pass" if not errors else "fail"


def _validate_claim_graph_projection(root: Path, claim_graph_payload: Mapping[str, Any] | None = None) -> tuple[list[str], str]:
    payload = claim_graph_payload or _load_json_object(root, CLAIM_GRAPH_JSON_ARTIFACT)
    if not isinstance(payload, Mapping):
        return ["AGG-HG3 claim graph missing"], "fail"
    errors = validate_terminal_node_projection(payload, root=root)
    return errors, "pass" if not errors else "fail"


def _validate_aggregate_owned_verdicts(index_payload: Mapping[str, Any] | None) -> tuple[list[str], str]:
    if index_payload is None:
        return ["AGG-HG4 index payload missing"], "fail"
    aggregate_sections = {
        "aggregation_consistency",
        "claim_verdicts",
        "claim_graph",
        "discovery_map",
        "negative_witness_summary",
        "quality_scorecard",
    }
    errors: list[str] = []
    for section_name, section in index_payload.items():
        if str(section_name) not in aggregate_sections:
            continue
        if not isinstance(section, Mapping):
            continue
        for key in section:
            key_text = str(key).lower()
            if "verdict" not in key_text:
                continue
            if key_text.endswith(("_pointer", "_pointers", "_ref", "_refs", "_owner")):
                continue
            if str(key) in {"hardgate_status"}:
                continue
            errors.append(f"AGG-HG4 aggregate-owned verdict field: $.{section_name}.{key}")
    return errors, "pass" if not errors else "fail"


def _line_has_boundary_or_correction_pointer(line: str) -> bool:
    return bool(BOUNDARY_POINTER_RE.search(line) and "reports/canonical/" in line and "$" in line)


def scan_doc_hg_surfaces(root: Path, paths: Sequence[Path | str] | None = None) -> AggregationConsistencyReport:
    selected = paths if paths is not None else DOC_HG_DEFAULT_PATHS
    errors: list[str] = []
    scanned = 0
    for raw_path in selected:
        candidate = raw_path if isinstance(raw_path, Path) else Path(raw_path)
        path = candidate if candidate.is_absolute() else root / candidate
        if not path.exists():
            continue
        scanned += 1
        lines = path.read_text(encoding="utf-8").splitlines()
        for line_no, line in enumerate(lines, start=1):
            for phrase in DOC_HG_FORBIDDEN_PHRASES:
                if phrase not in line:
                    continue
                window = " ".join(lines[max(0, line_no - 2) : min(len(lines), line_no + 1)])
                if not _line_has_boundary_or_correction_pointer(window):
                    rel = path.relative_to(root) if path.is_relative_to(root) else path
                    errors.append(f"DOC-HG forbidden phrase lacks boundary/correction pointer: {rel}:{line_no}:{phrase}")
    return AggregationConsistencyReport(
        errors=errors,
        hardgates={"DOC-HG": "pass" if not errors else "fail"},
        binding_count=0,
        doc_scan_count=scanned,
    )


def validate_aggregation_consistency(
    root: Path,
    *,
    index_payload: Mapping[str, Any] | None = None,
    claim_graph_payload: Mapping[str, Any] | None = None,
) -> AggregationConsistencyReport:
    payloads: dict[str, Any] = {}
    if index_payload is not None:
        payloads[INDEX_ARTIFACT] = index_payload
    elif (root / INDEX_ARTIFACT).exists():
        payloads[INDEX_ARTIFACT] = _load_json(root, INDEX_ARTIFACT)

    bindings = build_projection_bindings(root)
    errors: list[str] = []
    hardgates: dict[str, str] = {}

    binding_errors, hardgates["AGG-HG1"] = _validate_bindings(root, bindings, payloads)
    errors.extend(binding_errors)
    freshness_errors, hardgates["AGG-HG2"] = _validate_freshness(root)
    errors.extend(freshness_errors)
    graph_errors, hardgates["AGG-HG3"] = _validate_claim_graph_projection(root, claim_graph_payload)
    errors.extend(graph_errors)
    aggregate_errors, hardgates["AGG-HG4"] = _validate_aggregate_owned_verdicts(
        index_payload if index_payload is not None else payloads.get(INDEX_ARTIFACT)
    )
    errors.extend(aggregate_errors)
    doc_report = scan_doc_hg_surfaces(root)
    hardgates.update(doc_report.hardgates)
    errors.extend(doc_report.errors)

    return AggregationConsistencyReport(
        errors=errors,
        hardgates=hardgates,
        binding_count=len(bindings),
        doc_scan_count=doc_report.doc_scan_count,
    )
