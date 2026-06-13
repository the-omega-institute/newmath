"""Owner ledger for canonical evidence provenance."""

from __future__ import annotations

import ast
from dataclasses import asdict, dataclass, fields
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

SCHEMA_ID = "bedc-quality-lab:evidence-provenance"
OWNER = "bedc_quality_lab.evidence_provenance"
INDEX_ARTIFACT = "reports/canonical/index.json"
METRIC_SOURCE_TYPES = (
    "measured_training",
    "deterministic_projection",
    "declared_constant",
    "arm_branch",
    "protocol_field",
)
DISCOVERY_EVIDENCE_TYPES = (
    "empirical_training_clean",
    "empirical_training_tainted",
    "deterministic_projection",
    "protocol_artifact",
    "boundary_negative",
)
TRAINING_CLEAN_STATUS = "empirical_training_clean"
TRAINING_TAINTED_STATUS = "empirical_training_tainted"
TRAINING_ABSENT_STATUS = "training_evidence_absent"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_ROWS_BY_REPORT_KEY = "discovery_rows_by_report"

@dataclass(frozen=True)
class ProducerTrainingAudit:
    report: str
    producer_command: tuple[str, ...]
    producer_source_pointer: str | None
    backward_pointers: tuple[str, ...]
    optimizer_step_pointers: tuple[str, ...]
    parameter_update_pointers: tuple[str, ...]
    training_evidence_status: str
    not_claimed: tuple[str, ...]

    def as_dict(self) -> dict[str, Any]:
        return _json_ready_dict(self)


@dataclass(frozen=True)
class MetricProvenanceRow:
    report: str
    metric_name: str
    source_type: str
    source_code_pointer: str | None
    source_artifact_pointer: str
    producer_training_audit_pointer: str
    allowed_for_empirical_claim: bool
    value: Any
    not_claimed: tuple[str, ...]
    not_measurable_reason: str | None

    def as_dict(self) -> dict[str, Any]:
        return _json_ready_dict(self)


@dataclass(frozen=True)
class DiscoveryEvidenceRow:
    report: str
    evidence_type: str
    discovery_map_pointer: str | None
    metric_provenance_pointers: tuple[str, ...]
    producer_training_audit_pointer: str | None
    allowed_claim_kinds: tuple[str, ...]
    not_claimed: tuple[str, ...]

    def as_dict(self) -> dict[str, Any]:
        return _json_ready_dict(self)


def _json_ready_dict(row: Any) -> dict[str, Any]:
    return json.loads(json.dumps(asdict(row), sort_keys=True))


def evidence_provenance_pointer_for_report(report: str) -> str:
    return f"{INDEX_ARTIFACT}:$.evidence_provenance.{DISCOVERY_ROWS_BY_REPORT_KEY}.{report}"


def load_evidence_provenance(root: Path, *, require: bool = True) -> Mapping[str, Any] | None:
    path = root / INDEX_ARTIFACT
    if not path.exists():
        if require:
            raise ValueError("evidence provenance owner index is missing")
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, Mapping):
        if require:
            raise ValueError("canonical index must be a JSON object")
        return None
    section = payload.get("evidence_provenance")
    if not isinstance(section, Mapping):
        if require:
            raise ValueError("canonical index lacks evidence_provenance owner section")
        return None
    try:
        validate_evidence_provenance_payload(section)
    except ValueError:
        if require:
            raise
        return None
    return section


def owner_discovery_row(section: Mapping[str, Any], report: str) -> Mapping[str, Any] | None:
    rows_by_report = section.get(DISCOVERY_ROWS_BY_REPORT_KEY)
    if isinstance(rows_by_report, Mapping):
        row = rows_by_report.get(report)
        if isinstance(row, Mapping):
            return row
    rows = section.get("discovery_rows")
    if not isinstance(rows, list):
        return None
    matches = [row for row in rows if isinstance(row, Mapping) and row.get("report") == report]
    if len(matches) != 1:
        return None
    return matches[0]


def owner_metric_rows(section: Mapping[str, Any], report: str) -> list[Mapping[str, Any]]:
    rows = section.get("metric_rows")
    if not isinstance(rows, list):
        return []
    return [row for row in rows if isinstance(row, Mapping) and row.get("report") == report]


def owner_supports_empirical_claim(section: Mapping[str, Any], report: str) -> tuple[bool, str]:
    discovery = owner_discovery_row(section, report)
    if discovery is None:
        return False, "evidence-provenance-discovery-row-missing"
    if discovery.get("evidence_type") != "empirical_training_clean":
        return False, f"evidence-type-{discovery.get('evidence_type', 'missing')}"
    metric_rows = owner_metric_rows(section, report)
    if not metric_rows:
        return False, "metric-provenance-row-missing"
    if not all(row.get("allowed_for_empirical_claim") is True for row in metric_rows):
        return False, "metric-provenance-not-empirical"
    return True, ""


def validate_evidence_provenance_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("evidence provenance schema_id mismatch")
    if payload.get("owner") != OWNER:
        raise ValueError("evidence provenance owner mismatch")
    producer_rows = _require_object_rows(payload, "producer_audits")
    metric_rows = _require_object_rows(payload, "metric_rows")
    discovery_rows = _require_object_rows(payload, "discovery_rows")
    _require_dataclass_fields(producer_rows, "producer_audits", ProducerTrainingAudit)
    _require_dataclass_fields(metric_rows, "metric_rows", MetricProvenanceRow)
    _require_dataclass_fields(discovery_rows, "discovery_rows", DiscoveryEvidenceRow)
    _reject_empty_pointer_stubs(payload)
    producer_reports = [str(row.get("report")) for row in producer_rows if isinstance(row.get("report"), str)]
    if len(producer_reports) != len(producer_rows):
        raise ValueError("producer audit rows require report")
    if len(producer_reports) != len(set(producer_reports)):
        raise ValueError("producer audit report set contains duplicates")
    metric_reports = [str(row.get("report")) for row in metric_rows if isinstance(row.get("report"), str)]
    if len(metric_reports) != len(metric_rows):
        raise ValueError("metric provenance rows require report")
    if sorted(metric_reports) != sorted(producer_reports):
        raise ValueError("metric provenance report set must match producer audits")
    discovery_reports = [str(row.get("report")) for row in discovery_rows if isinstance(row.get("report"), str)]
    if len(discovery_reports) != len(discovery_rows):
        raise ValueError("discovery evidence rows require report")
    if len(discovery_reports) != len(set(discovery_reports)):
        raise ValueError("discovery evidence report set contains duplicates")
    if not set(producer_reports).issubset(set(discovery_reports)):
        raise ValueError("discovery evidence rows must cover producer audits")
    rows_by_report = payload.get(DISCOVERY_ROWS_BY_REPORT_KEY)
    if not isinstance(rows_by_report, Mapping):
        raise ValueError("evidence provenance discovery_rows_by_report must be an object")
    expected_rows_by_report = {str(row["report"]): row for row in discovery_rows}
    if dict(rows_by_report) != expected_rows_by_report:
        raise ValueError("evidence provenance discovery_rows_by_report must mirror discovery_rows")
    for row in metric_rows:
        source_type = row.get("source_type")
        if source_type not in METRIC_SOURCE_TYPES:
            raise ValueError(f"metric provenance source_type is unsupported: {source_type}")
        if source_type != "measured_training" and row.get("allowed_for_empirical_claim") is True:
            raise ValueError("non-training metric row cannot support empirical claims")
        if row.get("value") is None and not row.get("not_measurable_reason"):
            raise ValueError("null metric value requires not_measurable_reason")
        producer = _required_owner_row_pointer(
            payload,
            row.get("producer_training_audit_pointer"),
            collection="producer_audits",
            field="metric_rows.producer_training_audit_pointer",
        )
        if producer.get("report") != row.get("report"):
            raise ValueError("metric producer_training_audit_pointer must target the same report")
    for row in discovery_rows:
        evidence_type = row.get("evidence_type")
        if evidence_type not in DISCOVERY_EVIDENCE_TYPES:
            raise ValueError(f"discovery evidence_type is unsupported: {evidence_type}")
        if evidence_type != "empirical_training_clean" and "empirical_superiority" in row.get("allowed_claim_kinds", ()):
            raise ValueError("non-clean discovery evidence cannot support empirical superiority")
        report = str(row["report"])
        metric_pointers = row.get("metric_provenance_pointers")
        if not isinstance(metric_pointers, list):
            raise ValueError("discovery metric_provenance_pointers must be a list")
        if report in set(metric_reports) and not metric_pointers:
            raise ValueError("discovery metric_provenance_pointers must target metric rows for producer reports")
        if report not in set(metric_reports) and metric_pointers:
            raise ValueError("sidecar discovery rows cannot point to metric rows")
        for pointer in metric_pointers:
            metric = _required_owner_row_pointer(
                payload,
                pointer,
                collection="metric_rows",
                field="discovery_rows.metric_provenance_pointers",
            )
            if metric.get("report") != report:
                raise ValueError("discovery metric_provenance_pointers must target the same report")
        producer = _optional_owner_row_pointer(
            payload,
            row,
            "producer_training_audit_pointer",
            collection="producer_audits",
            field="discovery_rows.producer_training_audit_pointer",
        )
        if report in set(producer_reports):
            if producer is None:
                raise ValueError("discovery producer_training_audit_pointer is required for producer reports")
            if producer.get("report") != report:
                raise ValueError("discovery producer_training_audit_pointer must target the same report")
        elif producer is not None:
            raise ValueError("sidecar discovery rows must use null producer_training_audit_pointer")
    return dict(payload)


def build_evidence_provenance(
    *,
    root: Path,
    canonical_reports: Sequence[Any],
    generated_at: str,
) -> dict[str, Any]:
    producer_audits = [_producer_training_audit(root, spec, index) for index, spec in enumerate(canonical_reports)]
    producer_indices = {row.report: index for index, row in enumerate(producer_audits)}
    metric_rows = [
        _metric_provenance_row(root, spec, producer_audits[producer_indices[str(spec.name)]], producer_indices[str(spec.name)], index)
        for index, spec in enumerate(canonical_reports)
    ]
    metric_indices = {row.report: index for index, row in enumerate(metric_rows)}
    discovery_source_rows = _load_discovery_map_rows(root)
    reports_with_discovery = {str(row.get("report")) for row in discovery_source_rows if isinstance(row.get("report"), str)}
    discovery_rows = [
        _discovery_evidence_row(
            spec,
            source_row=_discovery_row_for_report(discovery_source_rows, str(spec.name)),
            source_index=_discovery_index_for_report(discovery_source_rows, str(spec.name)),
            producer_index=producer_indices[str(spec.name)],
            metric_index=metric_indices[str(spec.name)],
            metric_row=metric_rows[metric_indices[str(spec.name)]],
        )
        for spec in canonical_reports
    ]
    for source_index, source_row in enumerate(discovery_source_rows):
        report = source_row.get("report")
        if not isinstance(report, str) or report in producer_indices:
            continue
        discovery_rows.append(_sidecar_discovery_evidence_row(source_row, source_index))
    hardgate_status = _hardgate_status(producer_audits, metric_rows, discovery_rows, reports_with_discovery)
    discovery_row_dicts = [row.as_dict() for row in discovery_rows]
    payload = {
        "schema_id": SCHEMA_ID,
        "owner": OWNER,
        "generated_at": generated_at,
        "producer_audits": [row.as_dict() for row in producer_audits],
        "metric_rows": [row.as_dict() for row in metric_rows],
        "discovery_rows": discovery_row_dicts,
        DISCOVERY_ROWS_BY_REPORT_KEY: {str(row["report"]): row for row in discovery_row_dicts},
        "hardgate_status": hardgate_status,
        "artifact_pointers": {
            "owner_pointer": f"{INDEX_ARTIFACT}:$.evidence_provenance",
            "discovery_map_rows": f"{DISCOVERY_MAP_ARTIFACT}:$.rows",
        },
    }
    return validate_evidence_provenance_payload(payload)


def _require_object_rows(payload: Mapping[str, Any], key: str) -> list[Mapping[str, Any]]:
    rows = payload.get(key)
    if not isinstance(rows, list) or not all(isinstance(row, Mapping) for row in rows):
        raise ValueError(f"evidence provenance {key} must be object rows")
    return rows


def _require_dataclass_fields(rows: Sequence[Mapping[str, Any]], key: str, row_type: type[Any]) -> None:
    required = {field.name for field in fields(row_type)}
    for index, row in enumerate(rows):
        missing = sorted(required.difference(row.keys()))
        if missing:
            raise ValueError(f"evidence provenance {key}[{index}] requires fields: {', '.join(missing)}")


def _reject_empty_pointer_stubs(value: Any, path: str = "$") -> None:
    if isinstance(value, Mapping):
        for key, nested in value.items():
            nested_path = f"{path}.{key}"
            if key.endswith("_pointer") and nested == "":
                raise ValueError(f"evidence provenance pointer field must not be empty: {nested_path}")
            if key.endswith("_pointers") and isinstance(nested, list) and any(item == "" for item in nested):
                raise ValueError(f"evidence provenance pointer list must not contain empty entries: {nested_path}")
            _reject_empty_pointer_stubs(nested, nested_path)
    elif isinstance(value, list):
        for index, nested in enumerate(value):
            _reject_empty_pointer_stubs(nested, f"{path}[{index}]")


def _optional_owner_row_pointer(
    payload: Mapping[str, Any],
    row: Mapping[str, Any],
    key: str,
    *,
    collection: str,
    field: str,
) -> Mapping[str, Any] | None:
    if key not in row:
        raise ValueError(f"{field} must be present")
    pointer = row[key]
    if pointer is None:
        return None
    return _required_owner_row_pointer(payload, pointer, collection=collection, field=field)


def _required_owner_row_pointer(
    payload: Mapping[str, Any],
    pointer: Any,
    *,
    collection: str,
    field: str,
) -> Mapping[str, Any]:
    if not isinstance(pointer, str) or pointer == "":
        raise ValueError(f"{field} must be a non-empty owner pointer or null")
    prefix = f"{INDEX_ARTIFACT}:$.evidence_provenance.{collection}["
    if not pointer.startswith(prefix):
        raise ValueError(f"{field} must point to evidence_provenance.{collection}")
    target = _owner_pointer_value(payload, pointer)
    if not isinstance(target, Mapping):
        raise ValueError(f"{field} does not resolve")
    return target


def _owner_pointer_value(payload: Mapping[str, Any], pointer: str) -> Any:
    prefix = f"{INDEX_ARTIFACT}:$.evidence_provenance"
    if pointer == prefix:
        return payload
    if not pointer.startswith(f"{prefix}."):
        return None
    return _payload_pointer_value(payload, f"$.{pointer.removeprefix(f'{prefix}.')}")


def _payload_pointer_value(payload: Any, pointer: str) -> Any:
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        return None
    current = payload
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                if not isinstance(current, Mapping) or key not in current:
                    return None
                current = current[key]
            index_text = bracket[:-1]
            if not index_text.isdigit() or not isinstance(current, list):
                return None
            index = int(index_text)
            if index >= len(current):
                return None
            current = current[index]
            part = ""
        if not part:
            continue
        if isinstance(current, Mapping) and part in current:
            current = current[part]
        elif isinstance(current, list) and part.isdigit() and int(part) < len(current):
            current = current[int(part)]
        else:
            return None
    return current


def _producer_training_audit(root: Path, spec: Any, index: int) -> ProducerTrainingAudit:
    source_files = _producer_source_files(root, tuple(spec.command))
    source_pointer = _source_pointer(root, source_files[0]) if source_files else None
    backward: list[str] = []
    optimizer_steps: list[str] = []
    parameter_updates: list[str] = []
    for source_file in source_files:
        source_backward, source_steps, source_updates = _scan_training_lines(root, source_file)
        backward.extend(source_backward)
        optimizer_steps.extend(source_steps)
        parameter_updates.extend(source_updates)
    status = _training_status(backward, optimizer_steps, parameter_updates)
    not_claimed = () if status == TRAINING_CLEAN_STATUS else (
        "No producer-side backward pass plus optimizer step evidence is present in the static source audit.",
    )
    return ProducerTrainingAudit(
        report=str(spec.name),
        producer_command=tuple(str(part) for part in spec.command),
        producer_source_pointer=source_pointer,
        backward_pointers=tuple(backward),
        optimizer_step_pointers=tuple(optimizer_steps),
        parameter_update_pointers=tuple(parameter_updates),
        training_evidence_status=status,
        not_claimed=not_claimed,
    )


def _producer_source_files(root: Path, command: tuple[str, ...]) -> tuple[Path, ...]:
    if len(command) < 2:
        return ()
    command_source = root / command[1]
    if not command_source.exists():
        return ()
    source_files = [command_source]
    source_files.extend(_direct_local_import_files(root, command_source))
    unique: list[Path] = []
    seen: set[Path] = set()
    for source_file in source_files:
        resolved = source_file.resolve()
        if resolved not in seen and source_file.exists():
            unique.append(source_file)
            seen.add(resolved)
    return tuple(unique)


def _direct_local_import_files(root: Path, source_file: Path) -> tuple[Path, ...]:
    try:
        tree = ast.parse(source_file.read_text(encoding="utf-8"))
    except (OSError, SyntaxError):
        return ()
    result: list[Path] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module is not None:
            result.extend(_module_import_paths(root, node.module))
            for alias in node.names:
                result.extend(_module_import_paths(root, f"{node.module}.{alias.name}"))
        elif isinstance(node, ast.Import):
            for alias in node.names:
                result.extend(_module_import_paths(root, alias.name))
    return tuple(result)


def _module_import_paths(root: Path, module: str) -> tuple[Path, ...]:
    if not (module.startswith("bedc_quality_lab") or module.startswith("scripts")):
        return ()
    parts = module.split(".")
    file_path = root.joinpath(*parts).with_suffix(".py")
    init_path = root.joinpath(*parts, "__init__.py")
    paths = []
    if file_path.exists():
        paths.append(file_path)
    if init_path.exists():
        paths.append(init_path)
    return tuple(paths)


def _scan_training_lines(root: Path, source_file: Path) -> tuple[list[str], list[str], list[str]]:
    backward: list[str] = []
    optimizer_steps: list[str] = []
    parameter_updates: list[str] = []
    try:
        source_text = source_file.read_text(encoding="utf-8")
        tree = ast.parse(source_text)
    except (OSError, SyntaxError):
        return backward, optimizer_steps, parameter_updates
    nodes = sorted(ast.walk(tree), key=lambda node: (getattr(node, "lineno", 10**9), getattr(node, "col_offset", 0)))
    for node in nodes:
        line_number = getattr(node, "lineno", None)
        if not isinstance(line_number, int):
            continue
        pointer = _source_pointer(root, source_file, line_number)
        if isinstance(node, ast.Call) and _is_backward_call(node):
            _append_unique(backward, pointer)
        if isinstance(node, ast.Call) and _is_optimizer_step_call(node):
            _append_unique(optimizer_steps, pointer)
        if _is_parameter_update_node(node):
            _append_unique(parameter_updates, pointer)
    return backward, optimizer_steps, parameter_updates


def _append_unique(items: list[str], value: str) -> None:
    if value not in items:
        items.append(value)


def _is_backward_call(node: ast.Call) -> bool:
    return isinstance(node.func, ast.Attribute) and node.func.attr == "backward"


def _is_optimizer_step_call(node: ast.Call) -> bool:
    return (
        isinstance(node.func, ast.Attribute)
        and node.func.attr == "step"
        and _expr_mentions_token(node.func.value, ("optim", "optimizer", "opt"))
    )


def _is_parameter_update_node(node: ast.AST) -> bool:
    if isinstance(node, ast.AugAssign):
        return _expr_mentions_token(node.target, ("data", "grad", "parameter_update", "param_update"))
    if isinstance(node, ast.Attribute):
        return node.attr in {"grad", "requires_grad"}
    if isinstance(node, ast.Name):
        lowered = node.id.lower()
        return "parameter_update" in lowered or "param_update" in lowered
    if isinstance(node, ast.Call):
        call_path = _expr_path(node.func).lower()
        return "parameter_update" in call_path or "param_update" in call_path
    return False


def _expr_mentions_token(node: ast.AST, tokens: Sequence[str]) -> bool:
    lowered_tokens = tuple(token.lower() for token in tokens)
    return any(any(token in part for token in lowered_tokens) for part in _expr_parts(node))


def _expr_path(node: ast.AST) -> str:
    return ".".join(reversed(_expr_parts(node)))


def _expr_parts(node: ast.AST) -> tuple[str, ...]:
    if isinstance(node, ast.Name):
        return (node.id.lower(),)
    if isinstance(node, ast.Attribute):
        return (node.attr.lower(), *_expr_parts(node.value))
    if isinstance(node, ast.Call):
        return _expr_parts(node.func)
    if isinstance(node, ast.Subscript):
        return _expr_parts(node.value)
    return ()


def _source_pointer(root: Path, source_file: Path, line: int | None = None) -> str:
    try:
        relative = source_file.resolve().relative_to(root.resolve())
    except ValueError:
        relative = source_file
    suffix = "" if line is None else f":L{line}"
    return f"{relative.as_posix()}{suffix}"


def _training_status(backward: Sequence[str], optimizer_steps: Sequence[str], parameter_updates: Sequence[str]) -> str:
    if backward and optimizer_steps:
        return TRAINING_CLEAN_STATUS
    if backward or optimizer_steps or parameter_updates:
        return TRAINING_TAINTED_STATUS
    return TRAINING_ABSENT_STATUS


def _metric_provenance_row(
    root: Path,
    spec: Any,
    audit: ProducerTrainingAudit,
    producer_index: int,
    metric_index: int,
) -> MetricProvenanceRow:
    source_type = _metric_source_type(spec, audit)
    value, reason = _metric_value(root, spec)
    allowed = source_type == "measured_training" and audit.training_evidence_status == TRAINING_CLEAN_STATUS and value is not None
    not_claimed: tuple[str, ...] = ()
    if not allowed:
        not_claimed = (f"{source_type} metric rows do not certify empirical superiority.",)
    return MetricProvenanceRow(
        report=str(spec.name),
        metric_name="headline",
        source_type=source_type,
        source_code_pointer=audit.producer_source_pointer,
        source_artifact_pointer=f"{spec.json_artifact}:{spec.positive_claim_pointer}",
        producer_training_audit_pointer=f"{INDEX_ARTIFACT}:$.evidence_provenance.producer_audits[{producer_index}]",
        allowed_for_empirical_claim=allowed,
        value=value,
        not_claimed=not_claimed,
        not_measurable_reason=reason,
    )


def _metric_source_type(spec: Any, audit: ProducerTrainingAudit) -> str:
    name = str(spec.name)
    if name in {"dgt-l0-controls", "dgt-l1-controls"}:
        return "arm_branch"
    if name in {"dgt-base-undertraining-audit", "dgt-ablation-null-decomposition", "dgt-component-redundancy-audit"}:
        return "declared_constant"
    if name in {"order-k-benchmark", "claim-complexity", "mechanism-dna", "high-impact-review", "model-comparison"}:
        return "protocol_field" if name != "order-k-benchmark" else "deterministic_projection"
    if name in {"transformer-derivative-atlas", "lejepa-theorem-ledger", "causal-patch-suite"}:
        return "deterministic_projection"
    if audit.training_evidence_status == TRAINING_CLEAN_STATUS:
        return "measured_training"
    return "deterministic_projection"


def _metric_value(root: Path, spec: Any) -> tuple[Any, str | None]:
    artifact_path = root / str(spec.json_artifact)
    if not artifact_path.exists():
        return None, "source artifact is missing"
    try:
        payload = json.loads(artifact_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None, "source artifact is not valid JSON"
    value = pointer_value(payload, str(spec.positive_claim_pointer))
    if value is None:
        return None, "source artifact pointer is unresolved"
    return value, None


def pointer_value(payload: Any, pointer: str | None) -> Any:
    if pointer is None:
        return None
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        return None
    current = payload
    for part in pointer[2:].split("."):
        if isinstance(current, Mapping):
            if part not in current:
                return None
            current = current[part]
            continue
        if isinstance(current, list) and part.startswith("[") and part.endswith("]"):
            try:
                current = current[int(part[1:-1])]
            except (ValueError, IndexError):
                return None
            continue
        return None
    return current


def _load_discovery_map_rows(root: Path) -> list[Mapping[str, Any]]:
    path = root / DISCOVERY_MAP_ARTIFACT
    if not path.exists():
        return []
    from bedc_quality_lab.discovery_compiler.map import load_validated_discovery_map_payload

    payload = load_validated_discovery_map_payload(
        root,
        artifact=DISCOVERY_MAP_ARTIFACT,
        validate_owner_projection=False,
    )
    rows = payload.get("rows") if isinstance(payload, Mapping) else None
    if not isinstance(rows, list):
        raise ValueError("discovery map rows must be a list")
    return [row for row in rows if isinstance(row, Mapping)]


def _discovery_row_for_report(rows: Sequence[Mapping[str, Any]], report: str) -> Mapping[str, Any] | None:
    matches = [row for row in rows if row.get("report") == report]
    if len(matches) != 1:
        return None
    return matches[0]


def _discovery_index_for_report(rows: Sequence[Mapping[str, Any]], report: str) -> int | None:
    matches = [index for index, row in enumerate(rows) if row.get("report") == report]
    if len(matches) != 1:
        return None
    return matches[0]


def _discovery_evidence_row(
    spec: Any,
    *,
    source_row: Mapping[str, Any] | None,
    source_index: int | None,
    producer_index: int,
    metric_index: int,
    metric_row: MetricProvenanceRow,
) -> DiscoveryEvidenceRow:
    report = str(spec.name)
    discovery_pointer = _discovery_map_pointer(source_row, source_index)
    evidence_type = _classify_discovery_evidence(source_row, metric_row)
    allowed_claim_kinds = ("empirical_superiority",) if evidence_type == "empirical_training_clean" else _non_empirical_claim_kinds(evidence_type)
    return DiscoveryEvidenceRow(
        report=report,
        evidence_type=evidence_type,
        discovery_map_pointer=discovery_pointer,
        metric_provenance_pointers=(f"{INDEX_ARTIFACT}:$.evidence_provenance.metric_rows[{metric_index}]",),
        producer_training_audit_pointer=f"{INDEX_ARTIFACT}:$.evidence_provenance.producer_audits[{producer_index}]",
        allowed_claim_kinds=allowed_claim_kinds,
        not_claimed=() if allowed_claim_kinds == ("empirical_superiority",) else (f"{evidence_type} evidence does not certify empirical superiority.",),
    )


def _sidecar_discovery_evidence_row(source_row: Mapping[str, Any], index: int) -> DiscoveryEvidenceRow:
    return DiscoveryEvidenceRow(
        report=str(source_row.get("report")),
        evidence_type="boundary_negative",
        discovery_map_pointer=_discovery_map_pointer(source_row, index),
        metric_provenance_pointers=(),
        producer_training_audit_pointer=None,
        allowed_claim_kinds=("negative_boundary",),
        not_claimed=("Sidecar discovery rows are boundary evidence unless promoted by the owner ledger.",),
    )


def _classify_discovery_evidence(source_row: Mapping[str, Any] | None, metric_row: MetricProvenanceRow) -> str:
    if source_row is not None:
        if source_row.get("discovery_level") == "DN":
            return "boundary_negative"
        if source_row.get("audit_status") != "valid":
            return "boundary_negative"
    if metric_row.source_type == "measured_training":
        return "empirical_training_clean" if metric_row.allowed_for_empirical_claim else "empirical_training_tainted"
    if metric_row.source_type == "deterministic_projection":
        return "deterministic_projection"
    if metric_row.source_type in {"protocol_field", "declared_constant", "arm_branch"}:
        return "protocol_artifact"
    return "boundary_negative"


def discovery_evidence_type_for_report(
    *,
    root: Path,
    spec: Any,
    source_row: Mapping[str, Any] | None,
) -> str:
    audit = _producer_training_audit(root, spec, 0)
    metric = _metric_provenance_row(root, spec, audit, 0, 0)
    return _classify_discovery_evidence(source_row, metric)


def _discovery_map_pointer(source_row: Mapping[str, Any] | None, index: int | None) -> str | None:
    if source_row is None or index is None:
        return None
    report = source_row.get("report")
    if not isinstance(report, str):
        return None
    return f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}]"


def _non_empirical_claim_kinds(evidence_type: str) -> tuple[str, ...]:
    if evidence_type == "boundary_negative":
        return ("negative_boundary",)
    if evidence_type == "deterministic_projection":
        return ("projection_only",)
    return ("protocol_audit",)


def _hardgate_status(
    producer_audits: Sequence[ProducerTrainingAudit],
    metric_rows: Sequence[MetricProvenanceRow],
    discovery_rows: Sequence[DiscoveryEvidenceRow],
    reports_with_discovery: set[str],
) -> dict[str, dict[str, str]]:
    gates = {
        "EVCLASS-HG1": (
            len({row.report for row in producer_audits}) == len(producer_audits)
            and len(metric_rows) == len(producer_audits)
            and {row.report for row in metric_rows} == {row.report for row in producer_audits}
            and {row.report for row in producer_audits}.issubset({row.report for row in discovery_rows}),
            "every canonical report has one producer training audit row",
        ),
        "METRIC-HG1": (
            all(row.source_type in METRIC_SOURCE_TYPES for row in metric_rows),
            "headline metric rows use the owner source_type vocabulary",
        ),
        "METRIC-HG4": (
            all(row.value is not None or row.not_measurable_reason for row in metric_rows),
            "missing measurements are null with a reason",
        ),
        "DM-HG1": (
            all(row.evidence_type in DISCOVERY_EVIDENCE_TYPES for row in discovery_rows),
            "discovery rows use the owner evidence_type vocabulary",
        ),
        "DM-HG4": (
            reports_with_discovery.issubset({row.report for row in discovery_rows}),
            "committed discovery map rows have owner-backed rows",
        ),
    }
    return {
        gate_id: {
            "status": "pass" if passed else "fail",
            "reason": reason if passed else f"{reason}; fail-closed",
        }
        for gate_id, (passed, reason) in gates.items()
    }


def resolve_owner_pointer(root: Path, pointer: str) -> Any:
    from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer

    return resolve_artifact_pointer(root, pointer)
