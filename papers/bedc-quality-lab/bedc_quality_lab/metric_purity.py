"""Lab-local metric source and hardgate mutation purity audit."""

from __future__ import annotations

import ast
import copy
from dataclasses import asdict, dataclass
import importlib
import json
from pathlib import Path
import re
from types import ModuleType
from typing import Any, Callable, Iterable, Literal, Mapping, Sequence

from bedc_quality_lab import hardgate_inventory


SCHEMA_ID = "bedc.quality.metric_purity_audit"
TARGETS_SCHEMA_ID = "bedc.quality.metric_purity_targets"
ALLOWLIST_SCHEMA_ID = "bedc.quality.metric_purity_allowlist"
LAB_ROOT = Path(__file__).resolve().parents[1]
TARGET_KINDS = frozenset({"metric", "feature", "hardgate", "pathology"})
AST_SCANNED_KINDS = frozenset({"metric", "feature"})
OWNER_POINTER_BY_FAMILY = {
    "WIN": "bedc_quality_lab/winnability.py:build_payload",
}
AuditStage = Literal["full", "pre_generation", "post_generation"]
FINDING_CODES = frozenset(
    {f"METPURE-HG{index}" for index in range(1, 6)}
    | {f"AST-HG{index}" for index in range(1, 5)}
    | {f"MUT-HG{index}" for index in range(1, 5)}
    | {f"REG-HG{index}" for index in range(1, 6)}
)
IDENTITY_NAMES = frozenset(
    {
        "arm",
        "arm_id",
        "source_arm",
        "target_arm",
        "feature_mode",
        "component",
        "component_id",
        "component_name",
        "disabled_component",
    }
)
LABEL_NAMES = frozenset({"label", "labels", "target", "targets", "ground_truth", "y_true", "answer"})
SAFE_CALLS = frozenset(
    {
        "abs",
        "all",
        "any",
        "bool",
        "dict",
        "float",
        "int",
        "len",
        "list",
        "max",
        "min",
        "range",
        "round",
        "set",
        "sorted",
        "str",
        "sum",
        "tuple",
    }
)


@dataclass(**{"froz" + "en": True})
class MetricPurityTarget:
    id: str
    kind: Literal["metric", "feature", "hardgate", "pathology"]
    module: str
    callable: str
    owner_pointer: str
    report_artifact: str
    evidence_pointer: str
    empirical_metric_keys: tuple[str, ...]
    mutation_contract_refs: tuple[str, ...]
    allowlist_refs: tuple[str, ...]
    family: str = ""
    owner_surface: str = ""


@dataclass(**{"froz" + "en": True})
class MetricPurityFinding:
    target_id: str
    code: str
    path: str
    lineno: int
    symbol: str
    reason: str
    owner_pointer: str
    evidence_pointer: str
    allowlisted: bool = False


@dataclass(**{"froz" + "en": True})
class HardgateMutationCase:
    gate_id: str
    mutation_id: str
    owner_pointer: str
    apply: Mapping[str, Any]
    expected_failed_gate: str
    expected_reason_regex: str
    source_payload_pointer: str | None = None
    source_payload_factory: str | None = None


def default_targets_path(root: Path) -> Path:
    return Path(root) / "configs" / "metric_purity_targets.json"


def default_allowlist_path(root: Path) -> Path:
    return Path(root) / "configs" / "metric_purity_allowlist.json"


def iter_registered_hardgate_mutations(
    root: Path,
    targets_path: str | Path | None = None,
) -> tuple[HardgateMutationCase, ...]:
    resolved_targets_path = Path(targets_path) if targets_path is not None else default_targets_path(Path(root))
    findings: list[MetricPurityFinding] = []
    config, schema_ok = _validate_registry_schema(
        _load_json(resolved_targets_path),
        expected_schema_id=TARGETS_SCHEMA_ID,
        path=resolved_targets_path,
        code="REG-HG1",
        findings=findings,
    )
    if not schema_ok:
        raise ValueError("; ".join(finding.reason for finding in findings))
    config = _effective_target_config(Path(root), config)
    cases, case_findings = _load_hardgate_mutation_cases(config, path=resolved_targets_path)
    if case_findings:
        raise ValueError("; ".join(finding.reason for finding in case_findings))
    return cases


def evaluate_hardgate_mutation(root: Path, case: HardgateMutationCase) -> dict[str, Any]:
    try:
        payload = _resolve_mutation_source(Path(root), case)
    except Exception as exc:
        return {
            "status": "fail",
            "code": "MUT-HG2",
            "gate_id": case.gate_id,
            "mutation_id": case.mutation_id,
            "reason": str(exc),
        }
    try:
        evaluator = _resolve_owner_callable(case.owner_pointer)
        original_verdict = evaluator(payload)
    except Exception as exc:
        return {
            "status": "fail",
            "code": "MUT-HG3",
            "gate_id": case.gate_id,
            "mutation_id": case.mutation_id,
            "reason": str(exc),
        }
    original_status = _first_string(original_verdict, ("status",)) or "unknown"
    original_gate_status = _specific_gate_status(payload, original_verdict, case.gate_id)
    if original_status != "pass" or original_gate_status != "pass":
        return {
            "status": "fail",
            "code": "MUT-HG4",
            "gate_id": case.gate_id,
            "mutation_id": case.mutation_id,
            "owner_status": original_status,
            "failed_gate": _first_string(original_verdict, ("failed_gate", "failed_surface", "gate_id")),
            "reason": f"original gate {case.gate_id} was not passing",
            "expected_failed_gate": case.expected_failed_gate,
            "expected_reason_regex": case.expected_reason_regex,
        }
    try:
        mutated = copy.deepcopy(payload)
        _apply_mutation(mutated, case.apply)
    except Exception as exc:
        return {
            "status": "fail",
            "code": "MUT-HG2",
            "gate_id": case.gate_id,
            "mutation_id": case.mutation_id,
            "reason": str(exc),
        }
    try:
        verdict = evaluator(mutated)
    except Exception as exc:
        return {
            "status": "fail",
            "code": "MUT-HG3",
            "gate_id": case.gate_id,
            "mutation_id": case.mutation_id,
            "reason": str(exc),
        }
    failed_gate = _first_string(verdict, ("failed_gate", "failed_surface", "gate_id"))
    reason = _first_string(verdict, ("reason_code", "reason", "failed_reason", "failed_gate", "status"))
    owner_status = _first_string(verdict, ("status",)) or "unknown"
    matched_gate = failed_gate == case.expected_failed_gate
    matched_reason = re.search(case.expected_reason_regex, reason or "") is not None
    try:
        restored_verdict = evaluator(payload)
    except Exception as exc:
        return {
            "status": "fail",
            "code": "MUT-HG3",
            "gate_id": case.gate_id,
            "mutation_id": case.mutation_id,
            "reason": f"restore evaluation failed: {exc}",
        }
    restored_status = _first_string(restored_verdict, ("status",)) or "unknown"
    restored_gate_status = _specific_gate_status(payload, restored_verdict, case.gate_id)
    restored = restored_status == "pass" and restored_gate_status == "pass"
    passed = owner_status != "pass" and matched_gate and matched_reason and restored
    return {
        "status": "pass" if passed else "fail",
        "code": None if passed else "MUT-HG4",
        "gate_id": case.gate_id,
        "mutation_id": case.mutation_id,
        "owner_status": owner_status,
        "failed_gate": failed_gate,
        "reason": reason,
        "expected_failed_gate": case.expected_failed_gate,
        "expected_reason_regex": case.expected_reason_regex,
        "restored_owner_status": restored_status,
        "restored_gate_status": restored_gate_status,
    }


def run_metric_purity_audit(
    root: Path,
    targets_path: str | Path | None = None,
    allowlist_path: str | Path | None = None,
    *,
    target_ids: Iterable[str] | None = None,
    report_artifacts: Iterable[str] | None = None,
    audit_stage: AuditStage = "full",
) -> dict[str, Any]:
    root = Path(root)
    if audit_stage not in {"full", "pre_generation", "post_generation"}:
        raise ValueError(f"unknown metric purity audit stage: {audit_stage}")
    resolved_targets_path = Path(targets_path) if targets_path is not None else default_targets_path(root)
    resolved_allowlist_path = Path(allowlist_path) if allowlist_path is not None else default_allowlist_path(root)
    findings: list[MetricPurityFinding] = []
    target_config = _load_json(resolved_targets_path)
    allowlist_config = _load_json(resolved_allowlist_path) if resolved_allowlist_path.exists() else {"rows": []}
    target_config, target_schema_ok = _validate_registry_schema(
        target_config,
        expected_schema_id=TARGETS_SCHEMA_ID,
        path=resolved_targets_path,
        code="REG-HG1",
        findings=findings,
    )
    allowlist_config, allowlist_schema_ok = _validate_registry_schema(
        allowlist_config,
        expected_schema_id=ALLOWLIST_SCHEMA_ID,
        path=resolved_allowlist_path,
        code="REG-HG5",
        findings=findings,
    )
    if not target_schema_ok or not allowlist_schema_ok:
        return {
            "schema_id": SCHEMA_ID,
            "audit_stage": audit_stage,
            "targets": [],
            "findings": [_finding_record(finding) for finding in sorted(findings, key=_finding_sort_key)],
            "allowlist_hits": [],
            "allowlist_misses": [],
            "mutation_coverage": {"registered": 0, "by_gate": {}, "by_family": {}, "results": []},
            "pathology_results": [],
            "status": "fail",
        }
    target_config = _effective_target_config(root, target_config)
    all_targets = _load_targets(target_config, findings=findings, root=root)
    targets = _filter_targets(all_targets, target_ids=target_ids, report_artifacts=report_artifacts, audit_stage=audit_stage)
    allowlist_rows = _load_allowlist_rows(allowlist_config, findings=findings)
    allowlist_rows = _filter_allowlist_rows(allowlist_rows, targets, scoped=targets != all_targets)

    target_records = []
    pathology_results = []
    for target in targets:
        if target.kind != "pathology":
            target_findings = _audit_target(root, target, audit_stage=audit_stage)
            findings.extend(target_findings)
        if target.kind == "pathology":
            result, result_findings = _audit_pathology_target(root, target)
            pathology_results.append(result)
            findings.extend(result_findings)
        target_records.append(asdict(target))

    mutation_coverage, mutation_findings = _audit_mutations(
        root,
        targets,
        target_config,
        audit_stage=audit_stage,
        scoped=targets != all_targets,
    )
    findings.extend(mutation_findings)
    findings.extend(
        _audit_promoted_gate_registry(
            root,
            target_config,
            targets=targets,
            report_artifacts=report_artifacts,
            audit_stage=audit_stage,
        )
    )

    findings, allowlist_hits, allowlist_misses = _apply_allowlist(findings, allowlist_rows)
    unallowlisted = [finding for finding in findings if not finding.allowlisted]
    status = "pass" if not unallowlisted and not allowlist_misses else "fail"
    return {
        "schema_id": SCHEMA_ID,
        "audit_stage": audit_stage,
        "targets": target_records,
        "findings": [_finding_record(finding) for finding in sorted(findings, key=_finding_sort_key)],
        "allowlist_hits": allowlist_hits,
        "allowlist_misses": allowlist_misses,
        "mutation_coverage": mutation_coverage,
        "pathology_results": pathology_results,
        "status": status,
    }


def _audit_target(root: Path, target: MetricPurityTarget, *, audit_stage: AuditStage) -> list[MetricPurityFinding]:
    findings: list[MetricPurityFinding] = []
    try:
        resolved_callable, module = _resolve_target_callable(target)
    except Exception as exc:
        return [
            _finding(
                target,
                "REG-HG3",
                target.report_artifact or target.module,
                0,
                target.callable,
                f"registered callable cannot be resolved: {exc}",
            )
        ]
    if target.kind in AST_SCANNED_KINDS:
        findings.extend(_scan_callable_ast(target, module))
    if target.kind == "metric":
        if target.empirical_metric_keys:
            findings.extend(_audit_metric_projection(target, resolved_callable))
    if audit_stage != "pre_generation" and target.report_artifact:
        artifact = root / target.report_artifact
        if not artifact.exists() and target.kind != "pathology":
            findings.append(
                _finding(
                    target,
                    "REG-HG4",
                    target.report_artifact,
                    0,
                    target.report_artifact,
                    "registered report artifact is missing",
                )
            )
        elif target.kind != "pathology":
            findings.extend(_audit_evidence_pointer(root, target))
    return findings


def _filter_targets(
    targets: Sequence[MetricPurityTarget],
    *,
    target_ids: Iterable[str] | None,
    report_artifacts: Iterable[str] | None,
    audit_stage: AuditStage,
) -> tuple[MetricPurityTarget, ...]:
    del audit_stage
    id_set = None if target_ids is None else {str(item) for item in target_ids}
    artifact_set = None if report_artifacts is None else {str(item) for item in report_artifacts}
    if id_set is None and artifact_set is None:
        return tuple(targets)
    return tuple(
        target
        for target in targets
        if (id_set is not None and target.id in id_set)
        or (artifact_set is not None and target.report_artifact in artifact_set)
    )


def _filter_allowlist_rows(
    rows: Sequence[Mapping[str, Any]],
    targets: Sequence[MetricPurityTarget],
    *,
    scoped: bool,
) -> tuple[dict[str, Any], ...]:
    if not scoped:
        return tuple(dict(row) for row in rows)
    target_ids = {target.id for target in targets}
    return tuple(dict(row) for row in rows if str(row.get("target_id")) in target_ids)


def _audit_evidence_pointer(root: Path, target: MetricPurityTarget) -> list[MetricPurityFinding]:
    if not target.evidence_pointer:
        return [
            _finding(
                target,
                "REG-HG4",
                target.report_artifact,
                0,
                "evidence_pointer",
                "registered target has no evidence pointer",
            )
        ]
    exists, reason = _artifact_pointer_exists(root, target)
    if exists:
        return []
    return [
        _finding(
            target,
            "REG-HG4",
            target.evidence_pointer,
            0,
            target.evidence_pointer,
            reason,
        )
    ]


def _artifact_pointer_exists(root: Path, target: MetricPurityTarget) -> tuple[bool, str]:
    if target.evidence_pointer.startswith("$."):
        artifact = target.report_artifact
        pointer = target.evidence_pointer
    else:
        artifact, separator, pointer = target.evidence_pointer.partition(":")
        if not separator:
            return False, "registered evidence pointer is not an artifact-qualified JSON pointer"
    if not artifact:
        return False, "registered evidence pointer has no artifact path"
    path = root / artifact
    if not path.exists():
        return False, "registered evidence pointer artifact is missing"
    if path.suffix == ".jsonl":
        return _jsonl_pointer_exists(path, pointer)
    try:
        payload = _load_json(path)
    except Exception as exc:
        return False, f"registered evidence pointer artifact cannot be parsed: {exc}"
    if pointer == "$":
        return True, ""
    return _json_pointer_exists(payload, pointer)


def _jsonl_pointer_exists(path: Path, pointer: str) -> tuple[bool, str]:
    if not pointer.startswith("$.lines[") or not pointer.endswith("]"):
        return False, "registered JSONL evidence pointer must use $.lines[index]"
    index_text = pointer.removeprefix("$.lines[").removesuffix("]")
    if not index_text.isdigit():
        return False, "registered JSONL evidence pointer index is not numeric"
    try:
        line_count = sum(1 for line in path.read_text(encoding="utf-8").splitlines() if line)
    except Exception as exc:
        return False, f"registered JSONL evidence pointer artifact cannot be read: {exc}"
    return int(index_text) < line_count, "registered JSONL evidence pointer row is missing"


def _json_pointer_exists(payload: Any, pointer: str) -> tuple[bool, str]:
    if pointer in {"", "$"}:
        return True, ""
    if not pointer.startswith("$."):
        return False, f"unsupported evidence pointer: {pointer}"
    current_values = [payload]
    for part in pointer[2:].split("."):
        next_values: list[Any] = []
        for value in current_values:
            ok, resolved_values = _resolve_pointer_part(value, part)
            if not ok:
                return False, f"registered evidence pointer segment is missing: {part}"
            next_values.extend(resolved_values)
        if not next_values:
            return False, f"registered evidence pointer segment is empty: {part}"
        current_values = next_values
    return True, ""


def _resolve_pointer_part(value: Any, part: str) -> tuple[bool, list[Any]]:
    cursor_values = [value]
    remainder = part
    if "[" in remainder:
        key, bracket_text = remainder.split("[", 1)
        if key:
            keyed_values = []
            for cursor in cursor_values:
                if not isinstance(cursor, Mapping) or key not in cursor:
                    return False, []
                keyed_values.append(cursor[key])
            cursor_values = keyed_values
        while bracket_text:
            index_text, separator, rest = bracket_text.partition("]")
            if not separator:
                return False, []
            indexed_values: list[Any] = []
            for cursor in cursor_values:
                if not isinstance(cursor, list):
                    return False, []
                if index_text == "*":
                    if not cursor:
                        return False, []
                    indexed_values.extend(cursor)
                elif index_text.isdigit() and int(index_text) < len(cursor):
                    indexed_values.append(cursor[int(index_text)])
                else:
                    return False, []
            cursor_values = indexed_values
            if not rest:
                return True, cursor_values
            if not rest.startswith("["):
                return False, []
            bracket_text = rest[1:]
        return True, cursor_values
    resolved = []
    for cursor in cursor_values:
        if isinstance(cursor, Mapping) and part in cursor:
            resolved.append(cursor[part])
        elif isinstance(cursor, list) and part.isdigit() and int(part) < len(cursor):
            resolved.append(cursor[int(part)])
        else:
            return False, []
    return True, resolved


def _audit_pathology_target(root: Path, target: MetricPurityTarget) -> tuple[dict[str, Any], list[MetricPurityFinding]]:
    fixture_path = root / target.report_artifact
    findings: list[MetricPurityFinding] = []
    result = {
        "target_id": target.id,
        "fixture": target.report_artifact,
        "status": "blocked",
        "owner_status": None,
        "failed_surface": None,
        "reason_code": None,
    }
    try:
        fixture = _load_json(fixture_path)
    except Exception as exc:
        findings.append(_finding(target, "REG-HG4", target.report_artifact, 0, target.id, str(exc)))
        return result, findings
    expected_surface = str(fixture.get("expected_failed_surface", target.evidence_pointer))
    expected_reason = str(fixture.get("expected_reason_code", expected_surface))
    try:
        evaluator, _module = _resolve_target_callable(target)
        verdict = evaluator(fixture.get("payload", fixture))
    except Exception as exc:
        findings.append(_finding(target, "REG-HG3", target.report_artifact, 0, target.callable, str(exc)))
        result["reason_code"] = "owner-unavailable"
        return result, findings
    owner_status = _first_string(verdict, ("status",)) or "unknown"
    failed_surface = _first_failed_surface(verdict, expected_surface)
    reason_code = _failure_reason_code(verdict, failed_surface)
    result.update(
        {
            "owner_status": owner_status,
            "failed_surface": failed_surface,
            "reason_code": reason_code,
            "expected_failed_surface": expected_surface,
            "expected_reason_code": expected_reason,
        }
    )
    if owner_status != "pass" and failed_surface == expected_surface and reason_code == expected_reason:
        result["status"] = "pass"
        return result, findings
    result["status"] = "fail"
    findings.append(
        _finding(
            target,
            "METPURE-HG5",
            target.report_artifact,
            0,
            target.id,
            "pathology fixture did not fail through the expected owner surface and reason",
        )
    )
    return result, findings


def _audit_mutations(
    root: Path,
    targets: Sequence[MetricPurityTarget],
    target_config: Mapping[str, Any],
    *,
    audit_stage: AuditStage,
    scoped: bool,
) -> tuple[dict[str, Any], list[MetricPurityFinding]]:
    findings: list[MetricPurityFinding] = []
    hardgate_targets = tuple(target for target in targets if target.kind == "hardgate")
    selected_gate_refs = {
        ref
        for target in hardgate_targets
        for ref in (target.id, *target.mutation_contract_refs)
    }
    all_cases, case_findings = _load_hardgate_mutation_cases(target_config, path=default_targets_path(root))
    findings.extend(case_findings)
    if scoped:
        cases = tuple(
            case
            for case in all_cases
            if hardgate_targets
            and (case.gate_id in selected_gate_refs or _target_for_gate(hardgate_targets, case.gate_id) is not None)
        )
    else:
        cases = all_cases
    cases_by_gate: dict[str, list[HardgateMutationCase]] = {}
    cases_by_family: dict[str, list[HardgateMutationCase]] = {}
    if audit_stage == "pre_generation":
        return {
            "registered": len(cases),
            "by_gate": {key: len(value) for key, value in sorted(cases_by_gate.items())},
            "by_family": {key: len(value) for key, value in sorted(cases_by_family.items())},
            "results": [],
        }, findings
    for case in cases:
        cases_by_gate.setdefault(case.gate_id, []).append(case)
        target = _target_for_gate(hardgate_targets, case.gate_id)
        if target is not None and target.family:
            cases_by_family.setdefault(target.family, []).append(case)
    results = []
    for target in hardgate_targets:
        expected_refs = set(target.mutation_contract_refs or (target.id,))
        if not any(case.gate_id in expected_refs or case.gate_id == target.id for case in cases):
            findings.append(_finding(target, "MUT-HG1", target.report_artifact, 0, target.id, "registered hardgate has no mutation row"))
    for case in cases:
        result = evaluate_hardgate_mutation(root, case)
        results.append(result)
        if result["status"] != "pass":
            target = _target_for_gate(targets, case.gate_id)
            source_ref = case.source_payload_pointer or case.source_payload_factory or case.mutation_id
            findings.append(
                MetricPurityFinding(
                    target_id=target.id if target is not None else case.gate_id,
                    code=str(result.get("code") or "MUT-HG4"),
                    path=source_ref,
                    lineno=0,
                    symbol=case.mutation_id,
                    reason=str(result.get("reason") or "mutation contract failed"),
                    owner_pointer=case.owner_pointer,
                    evidence_pointer=source_ref,
                )
            )
    return {
        "registered": len(cases),
        "by_gate": {key: len(value) for key, value in sorted(cases_by_gate.items())},
        "by_family": {key: len(value) for key, value in sorted(cases_by_family.items())},
        "results": results,
    }, findings


def _audit_promoted_gate_registry(
    root: Path,
    target_config: Mapping[str, Any],
    *,
    targets: Sequence[MetricPurityTarget],
    report_artifacts: Iterable[str] | None,
    audit_stage: AuditStage,
) -> list[MetricPurityFinding]:
    if audit_stage == "pre_generation":
        return []
    artifact_filter = None if report_artifacts is None else {str(item) for item in report_artifacts}
    extra_surfaces = target_config.get("promotion_hardgate_surfaces", [])
    if not isinstance(extra_surfaces, list):
        extra_surfaces = []
    surfaces = tuple(
        surface
        for surface in hardgate_inventory.iter_promotion_hardgate_surfaces(root, extra_surfaces)
        if artifact_filter is None or surface.artifact in artifact_filter
    )
    if not surfaces:
        return []
    inventory_rows = hardgate_inventory.iter_hardgate_inventory(root, extra_surfaces)
    rows_by_surface: dict[str, list[hardgate_inventory.HardgateInventoryRow]] = {surface.surface_id: [] for surface in surfaces}
    for row in inventory_rows:
        if row.surface_id in rows_by_surface:
            rows_by_surface[row.surface_id].append(row)
    registry_refs = {target.id for target in targets if target.kind == "hardgate"}
    registry_refs.update(ref for target in targets if target.kind == "hardgate" for ref in target.mutation_contract_refs)
    cases, case_findings = _load_hardgate_mutation_cases(target_config, path=default_targets_path(root))
    mutation_refs = {case.gate_id for case in cases}
    findings = list(case_findings)
    for surface in surfaces:
        surface_path = root / surface.artifact
        if not surface_path.exists():
            continue
        rows = rows_by_surface.get(surface.surface_id, [])
        if not rows:
            findings.append(
                MetricPurityFinding(
                    target_id=surface.surface_id,
                    code="REG-HG4",
                    path=surface.artifact_pointer,
                    lineno=0,
                    symbol=surface.surface_id,
                    reason="promotion hardgate surface produced zero concrete rows",
                    owner_pointer=surface.owner_pointer,
                    evidence_pointer=surface.artifact_pointer,
                )
            )
            continue
        for row in rows:
            if row.gate_id not in registry_refs:
                findings.append(
                    MetricPurityFinding(
                        target_id=row.gate_id,
                        code="REG-HG1",
                        path=row.evidence_pointer,
                        lineno=0,
                        symbol=row.gate_id,
                        reason="promoted hardgate has no effective registry target",
                        owner_pointer=row.owner_pointer,
                        evidence_pointer=row.evidence_pointer,
                    )
                )
            if row.gate_id not in mutation_refs:
                findings.append(
                    MetricPurityFinding(
                        target_id=row.gate_id,
                        code="MUT-HG1",
                        path=row.evidence_pointer,
                        lineno=0,
                        symbol=row.gate_id,
                        reason="promoted hardgate has no mutation row",
                        owner_pointer=row.owner_pointer,
                        evidence_pointer=row.evidence_pointer,
                    )
                )
    return findings


def _scan_callable_ast(target: MetricPurityTarget, module: ModuleType) -> list[MetricPurityFinding]:
    source_path = Path(getattr(module, "__file__", "") or "")
    if not source_path.exists():
        return [_finding(target, "REG-HG4", target.module, 0, target.callable, "source file for registered callable is missing")]
    source = source_path.read_text(encoding="utf-8")
    tree = ast.parse(source)
    node = _find_callable_node(tree, target.callable)
    if node is None:
        return [_finding(target, "REG-HG4", _module_path(module), 0, target.callable, "registered callable source node is missing")]
    local_functions = {item.name for item in tree.body if isinstance(item, ast.FunctionDef)}
    allowed_helpers = set(target.allowlist_refs)
    findings: list[MetricPurityFinding] = []
    for child in ast.walk(node):
        if isinstance(child, (ast.If, ast.IfExp)) and _contains_identity_reference(child.test):
            findings.append(_ast_finding(target, module, "AST-HG1", child, target.callable, "control flow is keyed by arm, feature, or component identity"))
        elif isinstance(child, ast.Match) and _contains_identity_reference(child.subject):
            findings.append(_ast_finding(target, module, "AST-HG1", child, target.callable, "match dispatch is keyed by arm, feature, or component identity"))
        elif isinstance(child, ast.Subscript) and _contains_identity_reference(child.slice):
            findings.append(_ast_finding(target, module, "AST-HG2", child, target.callable, "lookup key depends on arm, feature, or component identity"))
        elif isinstance(child, ast.Dict) and _looks_like_identity_constant_table(child):
            findings.append(_ast_finding(target, module, "AST-HG2", child, target.callable, "numeric constant table is keyed by arm or component identity"))
        elif isinstance(child, (ast.Name, ast.Attribute, ast.Subscript)) and _contains_label_reference(child):
            findings.append(_ast_finding(target, module, "AST-HG3", child, target.callable, "metric source reads a label or target intermediate"))
        elif isinstance(child, ast.Call) and isinstance(child.func, ast.Name):
            helper = child.func.id
            if helper in local_functions and helper != _callable_leaf(target.callable) and helper not in allowed_helpers:
                findings.append(_ast_finding(target, module, "AST-HG4", child, helper, "metric source delegates to an unregistered local helper"))
            elif helper not in SAFE_CALLS and helper in local_functions and helper not in allowed_helpers:
                findings.append(_ast_finding(target, module, "AST-HG4", child, helper, "metric source delegates to an unregistered local helper"))
    return _dedupe_findings(findings)


def _audit_metric_projection(target: MetricPurityTarget, metric_callable: Callable[..., Any]) -> list[MetricPurityFinding]:
    original_rows = _sample_metric_rows()
    permuted_rows = [
        {**row, "arm_id": "control" if row["arm_id"] == "treatment" else "treatment"}
        for row in original_rows
    ]
    try:
        original = _call_metric_projection(metric_callable, original_rows)
        permuted = _call_metric_projection(metric_callable, permuted_rows)
    except Exception as exc:
        return [_finding(target, "METPURE-HG3", target.report_artifact or target.module, 0, target.callable, str(exc))]
    findings = []
    for key in target.empirical_metric_keys:
        left = _metric_value(original, key)
        right = _metric_value(permuted, key)
        if left is None or right is None:
            findings.append(_finding(target, "METPURE-HG2", target.report_artifact or target.module, 0, key, "registered empirical metric key is missing or non-numeric"))
        elif abs(left - right) > 1e-12:
            findings.append(_finding(target, "METPURE-HG1", target.report_artifact or target.module, 0, key, "metric value changes under arm-label permutation"))
    return findings


def _load_targets(config: Mapping[str, Any], *, findings: list[MetricPurityFinding], root: Path) -> tuple[MetricPurityTarget, ...]:
    rows = config.get("targets", [])
    if not isinstance(rows, list):
        findings.append(_registry_finding("REG-HG1", "configs/metric_purity_targets.json", "targets", "targets must be a list"))
        return ()
    targets = []
    seen = set()
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            findings.append(_registry_finding("REG-HG1", "configs/metric_purity_targets.json", f"targets[{index}]", "target row must be an object"))
            continue
        try:
            target = MetricPurityTarget(
                id=_required_str(row, "id"),
                kind=_kind(row),
                module=_required_str(row, "module"),
                callable=_required_str(row, "callable"),
                owner_pointer=_required_str(row, "owner_pointer"),
                report_artifact=str(row.get("report_artifact", "")),
                evidence_pointer=str(row.get("evidence_pointer", "")),
                empirical_metric_keys=tuple(str(item) for item in row.get("empirical_metric_keys", [])),
                mutation_contract_refs=tuple(str(item) for item in row.get("mutation_contract_refs", [])),
                allowlist_refs=tuple(str(item) for item in row.get("allowlist_refs", [])),
                family=str(row.get("family", "")),
                owner_surface=str(row.get("owner_surface", "")),
            )
        except ValueError as exc:
            findings.append(_registry_finding("REG-HG2", "configs/metric_purity_targets.json", f"targets[{index}]", str(exc)))
            continue
        if target.id in seen:
            findings.append(_registry_finding("REG-HG1", "configs/metric_purity_targets.json", target.id, "duplicate target id"))
            continue
        seen.add(target.id)
        targets.append(target)
    return tuple(targets)


def _effective_target_config(root: Path, config: Mapping[str, Any]) -> dict[str, Any]:
    extra_surfaces = config.get("promotion_hardgate_surfaces", [])
    if not isinstance(extra_surfaces, list):
        extra_surfaces = []
    if not isinstance(config.get("targets", []), list) or not isinstance(config.get("hardgate_mutations", []), list):
        return dict(config)
    static_targets = tuple(config.get("targets", []))
    static_mutations = (
        tuple(config.get("hardgate_mutations", []))
        if isinstance(config.get("hardgate_mutations", []), list)
        else ()
    )
    generated_targets = hardgate_inventory.generated_target_rows(root, extra_surfaces)
    generated_mutations = hardgate_inventory.generated_mutation_rows(root, extra_surfaces)
    targets_by_id: dict[str, Mapping[str, Any]] = {}
    for row in static_targets:
        if isinstance(row, Mapping):
            targets_by_id[str(row.get("id", ""))] = row
    for row in generated_targets:
        if isinstance(row, Mapping):
            targets_by_id[str(row.get("id", ""))] = _normalize_generated_target_row(row)
    mutation_keys: set[tuple[str, str]] = set()
    mutations = []
    for row in (*static_mutations, *generated_mutations):
        if not isinstance(row, Mapping):
            mutations.append(row)
            continue
        key = (str(row.get("gate_id", "")), str(row.get("mutation_id", "")))
        if key in mutation_keys:
            continue
        mutation_keys.add(key)
        mutations.append(row)
    return {
        **dict(config),
        "targets": [dict(targets_by_id[key]) for key in sorted(targets_by_id)],
        "hardgate_mutations": sorted(
            [dict(row) if isinstance(row, Mapping) else row for row in mutations],
            key=lambda row: (
                str(row.get("gate_id", "")) if isinstance(row, Mapping) else "",
                str(row.get("mutation_id", "")) if isinstance(row, Mapping) else "",
            ),
        ),
    }


def _normalize_generated_target_row(row: Mapping[str, Any]) -> Mapping[str, Any]:
    family = str(row.get("family", ""))
    owner_pointer = OWNER_POINTER_BY_FAMILY.get(family)
    if owner_pointer is None:
        return row
    return {**dict(row), "owner_pointer": owner_pointer}


def _load_hardgate_mutation_cases(config: Mapping[str, Any], *, path: Path) -> tuple[tuple[HardgateMutationCase, ...], list[MetricPurityFinding]]:
    findings: list[MetricPurityFinding] = []
    rows = config.get("hardgate_mutations", [])
    if not isinstance(rows, list):
        findings.append(_registry_finding("REG-HG1", path.as_posix(), "hardgate_mutations", "hardgate_mutations must be a list"))
        return (), findings
    cases = []
    seen: set[tuple[str, str]] = set()
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            findings.append(_registry_finding("REG-HG1", path.as_posix(), f"hardgate_mutations[{index}]", "mutation row must be an object"))
            continue
        try:
            case = _case_from_row(row)
        except (KeyError, ValueError) as exc:
            findings.append(_registry_finding("REG-HG1", path.as_posix(), f"hardgate_mutations[{index}]", str(exc)))
            continue
        key = (case.gate_id, case.mutation_id)
        if key in seen:
            findings.append(_registry_finding("REG-HG1", path.as_posix(), case.mutation_id, "duplicate mutation row"))
            continue
        seen.add(key)
        cases.append(case)
    return tuple(cases), findings


def _validate_registry_schema(
    config: Any,
    *,
    expected_schema_id: str,
    path: Path,
    code: str,
    findings: list[MetricPurityFinding],
) -> tuple[Mapping[str, Any], bool]:
    if not isinstance(config, Mapping):
        findings.append(_registry_finding(code, path.as_posix(), "schema_id", "registry payload must be an object"))
        return {}, False
    actual_schema_id = config.get("schema_id")
    if actual_schema_id != expected_schema_id:
        findings.append(
            _registry_finding(
                code,
                path.as_posix(),
                "schema_id",
                f"registry schema_id must be {expected_schema_id}",
            )
        )
        return config, False
    return config, True


def _load_allowlist_rows(config: Mapping[str, Any], *, findings: list[MetricPurityFinding]) -> tuple[dict[str, Any], ...]:
    rows = config.get("rows", [])
    if not isinstance(rows, list):
        findings.append(_registry_finding("REG-HG5", "configs/metric_purity_allowlist.json", "rows", "allowlist rows must be a list"))
        return ()
    cleaned = []
    required = {"target_id", "code", "path", "lineno", "symbol", "rationale", "owner_pointer"}
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping) or not required.issubset(row):
            findings.append(_registry_finding("REG-HG5", "configs/metric_purity_allowlist.json", f"rows[{index}]", "allowlist row is missing required cells"))
            continue
        if any(str(row[key]) in {"*", ""} for key in ("target_id", "code", "path", "symbol")):
            findings.append(_registry_finding("REG-HG5", "configs/metric_purity_allowlist.json", f"rows[{index}]", "allowlist row is broad or blank"))
            continue
        cleaned.append(dict(row))
    return tuple(cleaned)


def _apply_allowlist(
    findings: Sequence[MetricPurityFinding],
    rows: Sequence[Mapping[str, Any]],
) -> tuple[list[MetricPurityFinding], list[dict[str, Any]], list[dict[str, Any]]]:
    by_key = {_finding_allowlist_key(finding): finding for finding in findings}
    row_keys = {
        (
            str(row["target_id"]),
            str(row["code"]),
            str(row["path"]),
            int(row["lineno"]),
            str(row["symbol"]),
        ): row
        for row in rows
    }
    matched_keys = set(by_key) & set(row_keys)
    marked = [
        MetricPurityFinding(**{**asdict(finding), "allowlisted": _finding_allowlist_key(finding) in matched_keys})
        for finding in findings
    ]
    hits = [
        {
            "target_id": key[0],
            "code": key[1],
            "path": key[2],
            "lineno": key[3],
            "symbol": key[4],
            "owner_pointer": str(row_keys[key]["owner_pointer"]),
            "rationale": str(row_keys[key]["rationale"]),
        }
        for key in sorted(matched_keys)
    ]
    misses = [
        {
            "target_id": key[0],
            "code": key[1],
            "path": key[2],
            "lineno": key[3],
            "symbol": key[4],
            "owner_pointer": str(row_keys[key]["owner_pointer"]),
            "rationale": str(row_keys[key]["rationale"]),
            "reason": "allowlist row did not match a current finding",
        }
        for key in sorted(set(row_keys) - matched_keys)
    ]
    return marked, hits, misses


def _resolve_target_callable(target: MetricPurityTarget) -> tuple[Callable[..., Any], ModuleType]:
    module = importlib.import_module(target.module)
    value: Any = module
    for part in target.callable.split("."):
        value = getattr(value, part)
    if not callable(value):
        raise TypeError(f"{target.module}.{target.callable} is not callable")
    return value, module


def _resolve_owner_callable(owner_pointer: str) -> Callable[..., Any]:
    module_name, _, callable_name = owner_pointer.partition(":")
    if not callable_name:
        module_name, _, callable_name = owner_pointer.rpartition(".")
    module = importlib.import_module(module_name)
    value: Any = module
    for part in callable_name.split("."):
        value = getattr(value, part)
    if not callable(value):
        raise TypeError(f"{owner_pointer} is not callable")
    return value


def _case_from_row(row: Mapping[str, Any]) -> HardgateMutationCase:
    pointer = row.get("source_payload_pointer")
    factory = row.get("source_payload_factory")
    has_pointer = isinstance(pointer, str) and bool(pointer)
    has_factory = isinstance(factory, str) and bool(factory)
    if has_pointer == has_factory:
        raise ValueError("exactly one of source_payload_pointer or source_payload_factory is required")
    apply_ops = row.get("apply", {})
    if not isinstance(apply_ops, Mapping):
        raise ValueError("apply must be an object")
    return HardgateMutationCase(
        gate_id=_required_str(row, "gate_id"),
        mutation_id=_required_str(row, "mutation_id"),
        owner_pointer=_required_str(row, "owner_pointer"),
        apply=dict(apply_ops),
        expected_failed_gate=_required_str(row, "expected_failed_gate"),
        expected_reason_regex=_required_str(row, "expected_reason_regex"),
        source_payload_pointer=str(pointer) if has_pointer else None,
        source_payload_factory=str(factory) if has_factory else None,
    )


def _resolve_mutation_source(root: Path, case: HardgateMutationCase) -> Any:
    if case.source_payload_pointer is not None:
        return _resolve_artifact_pointer(root, case.source_payload_pointer)
    if case.source_payload_factory is None:
        raise ValueError("mutation case has no source payload")
    factory = _resolve_owner_callable(case.source_payload_factory)
    try:
        return factory(case.gate_id)
    except TypeError:
        try:
            return factory(gate_id=case.gate_id)
        except TypeError:
            return factory()


def _apply_mutation(payload: Any, operations: Mapping[str, Any]) -> None:
    for pointer, value in operations.get("set", {}).items():
        _set_pointer(payload, str(pointer), value)
    for pointer in operations.get("delete", []):
        _delete_pointer(payload, str(pointer))


def _set_pointer(payload: Any, pointer: str, value: Any) -> None:
    parent, key = _pointer_parent(payload, pointer)
    if isinstance(parent, list):
        parent[int(key)] = value
    else:
        parent[key] = value


def _delete_pointer(payload: Any, pointer: str) -> None:
    parent, key = _pointer_parent(payload, pointer)
    if isinstance(parent, list):
        del parent[int(key)]
    else:
        del parent[key]


def _pointer_parent(payload: Any, pointer: str) -> tuple[Any, str]:
    parts = _pointer_parts(pointer)
    if not parts:
        raise ValueError("cannot mutate the root pointer")
    current = payload
    for part in parts[:-1]:
        current = current[int(part)] if isinstance(current, list) else current[part]
    return current, parts[-1]


def _resolve_artifact_pointer(root: Path, artifact_pointer: str) -> Any:
    artifact, _, pointer = artifact_pointer.partition(":")
    if not pointer:
        pointer = "$"
    payload = _load_json(root / artifact)
    current: Any = payload
    for part in _pointer_parts(pointer):
        current = current[int(part)] if isinstance(current, list) else current[part]
    return current


def _specific_gate_status(payload: Any, verdict: Any, gate_id: str) -> str | None:
    for container in (_field_value(payload, "gates"), _field_value(verdict, "gates")):
        if isinstance(container, Mapping):
            row = container.get(gate_id)
            if isinstance(row, Mapping) and isinstance(row.get("status"), str):
                return str(row["status"])
    if _first_string(verdict, ("failed_gate", "failed_surface", "gate_id")) == gate_id:
        return "fail"
    status = _first_string(verdict, ("status",))
    return "pass" if status == "pass" else None


def _pointer_parts(pointer: str) -> list[str]:
    if pointer in {"", "$"}:
        return []
    if not pointer.startswith("$."):
        raise ValueError(f"unsupported pointer: {pointer}")
    return pointer[2:].split(".")


def _call_metric_projection(metric_callable: Callable[..., Any], rows: Sequence[Mapping[str, Any]]) -> Mapping[str, Any]:
    errors = []
    for payload in (list(rows), {"rows": list(rows)}, rows[0]):
        try:
            result = metric_callable(payload)
        except TypeError as exc:
            errors.append(str(exc))
            continue
        if not isinstance(result, Mapping):
            raise TypeError("registered metric projection returned a non-mapping")
        return result
    raise TypeError("; ".join(errors) or "registered metric projection has an unsupported signature")


def _metric_value(payload: Mapping[str, Any], key: str) -> float | None:
    for item_key, value in _walk_items(payload):
        if item_key == key and isinstance(value, (int, float)) and not isinstance(value, bool):
            return float(value)
    return None


def _walk_items(value: Any) -> Iterable[tuple[str, Any]]:
    if isinstance(value, Mapping):
        for key, item in value.items():
            yield str(key), item
            yield from _walk_items(item)
    elif isinstance(value, list):
        for item in value:
            yield from _walk_items(item)


def _sample_metric_rows() -> list[dict[str, Any]]:
    return [
        {
            "arm_id": "treatment",
            "feature_mode": "shared",
            "component_name": "shared_component",
            "score": 0.7,
            "loss": 0.3,
            "label": 1,
        },
        {
            "arm_id": "treatment",
            "feature_mode": "shared",
            "component_name": "shared_component",
            "score": 0.6,
            "loss": 0.4,
            "label": 1,
        },
        {
            "arm_id": "control",
            "feature_mode": "shared",
            "component_name": "shared_component",
            "score": 0.5,
            "loss": 0.5,
            "label": 0,
        },
    ]


def _find_callable_node(tree: ast.Module, callable_name: str) -> ast.AST | None:
    leaf = _callable_leaf(callable_name)
    class_name = callable_name.split(".")[-2] if "." in callable_name else None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == leaf:
            if class_name is None:
                return node
            parent = _parent_class(tree, node)
            if parent == class_name:
                return node
    return None


def _parent_class(tree: ast.Module, target_node: ast.AST) -> str | None:
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef) and any(child is target_node for child in ast.walk(node)):
            return node.name
    return None


def _callable_leaf(callable_name: str) -> str:
    return callable_name.split(".")[-1]


def _contains_identity_reference(node: ast.AST) -> bool:
    return any(_identity_reference(child) for child in ast.walk(node))


def _contains_label_reference(node: ast.AST) -> bool:
    return any(_label_reference(child) for child in ast.walk(node))


def _identity_reference(node: ast.AST) -> bool:
    if isinstance(node, ast.Name):
        return node.id in IDENTITY_NAMES
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value in IDENTITY_NAMES
    if isinstance(node, ast.Attribute):
        return node.attr in IDENTITY_NAMES
    return False


def _label_reference(node: ast.AST) -> bool:
    if isinstance(node, ast.Name):
        return node.id in LABEL_NAMES
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value in LABEL_NAMES
    if isinstance(node, ast.Attribute):
        return node.attr in LABEL_NAMES
    return False


def _looks_like_identity_constant_table(node: ast.Dict) -> bool:
    if not node.keys or not node.values:
        return False
    key_hits = 0
    numeric_values = 0
    for key, value in zip(node.keys, node.values):
        if isinstance(key, ast.Constant) and isinstance(key.value, str):
            lowered = key.value.lower()
            if any(token in lowered for token in ("arm", "control", "treatment", "matched", "drt", "component", "without", "full")):
                key_hits += 1
        if isinstance(value, ast.Constant) and isinstance(value.value, (int, float)) and not isinstance(value.value, bool):
            numeric_values += 1
    return key_hits > 0 and numeric_values > 0


def _target_for_gate(targets: Sequence[MetricPurityTarget], gate_id: str) -> MetricPurityTarget | None:
    for target in targets:
        if target.id == gate_id or gate_id in target.mutation_contract_refs:
            return target
    return None


def _first_string(payload: Any, keys: Sequence[str]) -> str | None:
    for key in keys:
        value = _field_value(payload, key)
        if isinstance(value, str):
            return value
    return None


def _field_value(payload: Any, key: str) -> Any:
    if isinstance(payload, Mapping):
        return payload.get(key)
    return getattr(payload, key, None)


def _first_failed_surface(payload: Any, expected_surface: str) -> str | None:
    explicit = _first_string(payload, ("failed_surface", "failed_gate", "surface", "gate_id"))
    if explicit is not None:
        return explicit
    failed_gates = _field_value(payload, "failed_gates")
    if isinstance(failed_gates, Sequence) and not isinstance(failed_gates, (str, bytes, bytearray)):
        gate_ids = tuple(str(gate_id) for gate_id in failed_gates)
        if expected_surface in gate_ids:
            return expected_surface
        if gate_ids:
            return gate_ids[0]
    return None


def _failure_reason_code(payload: Any, failed_surface: str | None) -> str | None:
    explicit = _first_string(payload, ("reason_code", "failed_reason", "reason"))
    if explicit is not None:
        return explicit
    if failed_surface is None:
        return None
    gates = _field_value(payload, "gates")
    if isinstance(gates, Mapping) and failed_surface in gates:
        return failed_surface
    failed_gates = _field_value(payload, "failed_gates")
    if isinstance(failed_gates, Sequence) and not isinstance(failed_gates, (str, bytes, bytearray)):
        if failed_surface in {str(gate_id) for gate_id in failed_gates}:
            return failed_surface
    return None


def _required_str(row: Mapping[str, Any], key: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value:
        raise ValueError(f"{key} must be a non-empty string")
    return value


def _kind(row: Mapping[str, Any]) -> Literal["metric", "feature", "hardgate", "pathology"]:
    value = _required_str(row, "kind")
    if value not in TARGET_KINDS:
        raise ValueError(f"unknown target kind: {value}")
    return value  # type: ignore[return-value]


def _load_json(path: Path) -> Any:
    with Path(path).open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _finding(
    target: MetricPurityTarget,
    code: str,
    path: str,
    lineno: int,
    symbol: str,
    reason: str,
) -> MetricPurityFinding:
    return MetricPurityFinding(
        target_id=target.id,
        code=code,
        path=path,
        lineno=int(lineno),
        symbol=symbol,
        reason=reason,
        owner_pointer=target.owner_pointer,
        evidence_pointer=target.evidence_pointer,
    )


def _ast_finding(
    target: MetricPurityTarget,
    module: ModuleType,
    code: str,
    node: ast.AST,
    symbol: str,
    reason: str,
) -> MetricPurityFinding:
    return _finding(target, code, _module_path(module), int(getattr(node, "lineno", 0)), symbol, reason)


def _registry_finding(code: str, path: str, symbol: str, reason: str) -> MetricPurityFinding:
    return MetricPurityFinding(
        target_id="metric-purity-registry",
        code=code,
        path=path,
        lineno=0,
        symbol=symbol,
        reason=reason,
        owner_pointer="configs/metric_purity_targets.json:$",
        evidence_pointer=path,
    )


def _finding_record(finding: MetricPurityFinding) -> dict[str, Any]:
    return asdict(finding)


def _finding_sort_key(finding: MetricPurityFinding) -> tuple[Any, ...]:
    return (finding.target_id, finding.code, finding.path, finding.lineno, finding.symbol)


def _finding_allowlist_key(finding: MetricPurityFinding) -> tuple[str, str, str, int, str]:
    return (finding.target_id, finding.code, finding.path, int(finding.lineno), finding.symbol)


def _dedupe_findings(findings: Sequence[MetricPurityFinding]) -> list[MetricPurityFinding]:
    by_key = {_finding_sort_key(finding): finding for finding in findings}
    return [by_key[key] for key in sorted(by_key)]


def _module_path(module: ModuleType) -> str:
    path = Path(getattr(module, "__file__", "") or "")
    if path:
        try:
            return path.resolve().relative_to(LAB_ROOT).as_posix()
        except ValueError:
            return path.as_posix()
    return getattr(module, "__name__", "unknown")
