"""Canonical negative discovery reports."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .claim_verdict_reason import (
    reason_basis_from_negative_owner,
    reason_for_claim_verdict,
    validate_claim_verdict_reason,
)
from .map import load_validated_discovery_map_payload
from .pointers import pointer_value, resolve_artifact_pointer, split_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:negative-discovery-reports"
ARTIFACT_ID = "bedc-quality-lab:negative-discovery-reports"
JSON_ARTIFACT = "reports/canonical/negative_discovery_reports.json"
MARKDOWN_ARTIFACT = "reports/canonical/negative_discovery_reports.md"
NEGATIVE_WITNESS_SUMMARY_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
SUMMARY_SCHEMA_ID = "bedc-quality-lab:discovery-negative-witness-summary"
SUMMARY_ARTIFACT_ID = "bedc-quality-lab:discovery-negative-witness-summary"
SUMMARY_JSON_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.json"
SUMMARY_MARKDOWN_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.md"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
CLAIM_VERDICTS_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
POSITIVE_BASE_LEVELS = frozenset({"D4", "D5-O", "D5-M"})
DIMENSION_MISMATCH_REPORT_ID = "dimension-mismatch-scale-leakage"
DIMENSION_MISMATCH_GAP_WITNESS_POINTER = (
    "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:"
    "$.run_local.negative_witness[0]"
)
DIMENSION_MISMATCH_REGRESSION_NODEID = (
    "tests/test_dimension_mismatch_debt_transfer.py::test_scale_leakage_sidecar_maps_to_first_negative_witness"
)
DERIVATIVE_DN_REPORT_IDS = frozenset({"transformer-derivative-atlas"})
REQUIRED_NEGATIVE_REPORT_IDS = frozenset(
    {
        "certificate-guided-training",
        "gap-head-ablation",
        "spectral-ablation-hinge",
        DIMENSION_MISMATCH_REPORT_ID,
        "single-threshold-escape",
        "training-choice-observability",
    }
)
OWNER_FACT_KEYS = frozenset(
    {
        "negative_id",
        "report_id",
        "claim_id",
        "kind",
        "report",
        "source",
        "json_artifact",
        "markdown_artifact",
        "ledger_pointer",
        "discovery_level",
        "base_level",
        "effective_level",
        "terminal_verdict",
        "classifier_reasons",
        "projection_status",
        "evidence_pointer",
        "failed_gate",
        "debt_row_pointer",
        "anti_triviality_status",
        "anti_triviality_policy",
        "anti_triviality_recommended_level",
        "anti_triviality_failed_gate",
        "anti_triviality_gate_evidence",
        "downgrade_reason",
        "hypothesis",
        "what_was_learned",
        "next_hypothesis",
        "stop_reason",
        "not_claimed",
        "discovery_map_pointer",
        "claim_verdict_pointer",
        "audit_status",
        "audit_reason",
        "bedc_gap_mapping",
    }
)

BEDC_GAP_MAPPING_KEYS = (
    "witness_pointer",
    "bedc_gap_field",
    "demotion_rule",
    "regression_test",
)


@dataclass(frozen=True)
class BedcGapMapping:
    witness_pointer: str
    bedc_gap_field: str
    demotion_rule: str
    regression_test: str

    @classmethod
    def from_witness_pointer(cls, root: Path, pointer: str) -> "BedcGapMapping":
        witness = resolve_artifact_pointer(root, pointer)
        if not isinstance(witness, Mapping):
            raise ValueError(f"BEDC gap mapping witness pointer does not resolve: {pointer}")
        values = {
            key: witness.get(key)
            for key in ("bedc_gap_field", "demotion_rule", "regression_test")
        }
        missing = [key for key, value in values.items() if not isinstance(value, str) or not value]
        if missing:
            raise ValueError(f"BEDC gap mapping witness missing cells: {', '.join(missing)}")
        regression_nodeid = _resolve_witness_local_pointer(root, pointer, str(values["regression_test"]))
        if regression_nodeid != DIMENSION_MISMATCH_REGRESSION_NODEID:
            raise ValueError("BEDC gap mapping regression test pointer does not resolve to the expected nodeid")
        return cls(
            witness_pointer=pointer,
            bedc_gap_field=str(values["bedc_gap_field"]),
            demotion_rule=str(values["demotion_rule"]),
            regression_test=str(values["regression_test"]),
        )

    def as_owner_cell(self) -> dict[str, str]:
        return {
            "witness_pointer": self.witness_pointer,
            "bedc_gap_field": self.bedc_gap_field,
            "demotion_rule": self.demotion_rule,
            "regression_test": self.regression_test,
        }

    @classmethod
    def validate_owner_cell(cls, root: Path, owner_row: Mapping[str, Any]) -> None:
        cell = owner_row.get("bedc_gap_mapping")
        if not isinstance(cell, Mapping):
            raise ValueError("dimension mismatch DN report requires bedc_gap_mapping")
        if set(cell) != set(BEDC_GAP_MAPPING_KEYS):
            raise ValueError("dimension mismatch bedc_gap_mapping has unsupported shape")
        pointer = cell.get("witness_pointer")
        if not isinstance(pointer, str) or not pointer:
            raise ValueError("dimension mismatch bedc_gap_mapping requires witness_pointer")
        expected = cls.from_witness_pointer(root, pointer).as_owner_cell()
        actual = {key: cell.get(key) for key in BEDC_GAP_MAPPING_KEYS}
        if actual != expected:
            raise ValueError("dimension mismatch bedc_gap_mapping does not match source witness")


def _validate_dimension_mismatch_scale_leakage_mapping(root: Path, item: Mapping[str, Any]) -> None:
    BedcGapMapping.validate_owner_cell(root, item)
    mapping = item["bedc_gap_mapping"]
    witness_pointer = mapping["witness_pointer"]
    witness = resolve_artifact_pointer(root, witness_pointer)
    if not isinstance(witness, Mapping):
        raise ValueError("dimension mismatch bedc_gap_mapping witness_pointer does not resolve")
    if witness.get("witness_id") != "scale_leakage_witness":
        raise ValueError("dimension mismatch bedc_gap_mapping requires scale_leakage_witness")
    if witness.get("bedc_gap_field") != "representation_scale_leakage":
        raise ValueError("dimension mismatch bedc_gap_mapping requires representation_scale_leakage")
    if witness.get("demotion_rule") != "demote_to_DN_or_D1":
        raise ValueError("dimension mismatch bedc_gap_mapping requires demote_to_DN_or_D1")
    if witness.get("status") != "valid":
        raise ValueError("dimension mismatch bedc_gap_mapping witness status is not valid")
    regression_test = witness.get("regression_test")
    if not isinstance(regression_test, str) or _resolve_witness_local_pointer(root, witness_pointer, regression_test) is None:
        raise ValueError("dimension mismatch bedc_gap_mapping regression_test does not resolve")
    source_artifact = witness.get("source_artifact")
    source_pointer = witness.get("source_pointer")
    if not isinstance(source_artifact, str) or not isinstance(source_pointer, str):
        raise ValueError("dimension mismatch bedc_gap_mapping source pointer is malformed")
    source_value = resolve_artifact_pointer(root, f"{source_artifact}:{source_pointer}")
    if source_value != "scale_leakage_detected":
        raise ValueError("dimension mismatch bedc_gap_mapping source pointer is not scale_leakage_detected")
    source_status_pointer = item.get("failed_gate")
    json_artifact = item.get("json_artifact")
    if not isinstance(source_status_pointer, str) or not isinstance(json_artifact, str):
        raise ValueError("dimension mismatch DN report source status pointer is malformed")
    if resolve_artifact_pointer(root, f"{json_artifact}:{source_status_pointer}") != "scale_leakage_detected":
        raise ValueError("dimension mismatch DN report source status is not scale_leakage_detected")


def _resolve_witness_local_pointer(root: Path, witness_pointer: str, pointer: str) -> Any:
    if not pointer.startswith("$."):
        return resolve_artifact_pointer(root, pointer) if ":$" in pointer else pointer
    split = split_artifact_pointer(witness_pointer)
    if split is None:
        return None
    artifact, _ = split
    payload = _load_json(root, artifact)
    return pointer_value(payload, pointer)


def _timestamp(generated_at: str | None) -> str:
    return generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()


def _load_json(root: Path, artifact: str) -> dict[str, Any]:
    path = root / artifact
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"source artifact must be a JSON object: {artifact}")
    return payload


def _load_jsonl(root: Path, artifact: str) -> list[dict[str, Any]]:
    path = root / artifact
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines()):
        row = json.loads(line)
        if not isinstance(row, dict):
            raise ValueError(f"source row must be a JSON object: {artifact}:{index}")
        rows.append(row)
    return rows


def _source_from_map_row(row: Mapping[str, Any]) -> str:
    pointer = row.get("failed_gate") or row.get("debt_row_pointer") or row.get("evidence_pointer")
    artifact = str(row.get("json_artifact") or "")
    return artifact if not isinstance(pointer, str) or not pointer else f"{artifact}:{pointer}"


def _canonical_report_id(row: Mapping[str, Any]) -> str:
    value = row.get("report_id")
    if isinstance(value, str) and value:
        return value
    report = str(row.get("report") or "").removeprefix("dn:")
    if report == "dimension-mismatch-debt-transfer":
        return "dimension-mismatch-scale-leakage"
    return report


def _canonical_negative_id(report_id: str) -> str:
    return f"dn:{report_id}"


def _is_nonempty(value: Any) -> bool:
    if value is None:
        return False
    if isinstance(value, str):
        return bool(value)
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return bool(value)
    return True


def validate_negative_report_row(root: Path, row: Mapping[str, Any]) -> dict[str, Any]:
    item = dict(row)
    report_id = _canonical_report_id(item)
    if not report_id:
        raise ValueError("negative discovery report row requires report_id")
    item["report_id"] = report_id
    item["negative_id"] = _canonical_negative_id(report_id)
    item.setdefault("kind", "discovery_report")
    item.setdefault("claim_id", f"claim:{item.get('report') or report_id}")
    item.setdefault("discovery_level", "DN")
    item.setdefault("discovery_map_pointer", None)
    item.setdefault("claim_verdict_pointer", None)
    item.setdefault("audit_reason", "")
    item.setdefault("audit_status", "pass")
    item.setdefault("ledger_pointer", item.get("source"))

    if item["kind"] != "discovery_report":
        raise ValueError(f"negative discovery report row has unsupported kind: {item['kind']}")
    if item["discovery_level"] != "DN":
        raise ValueError(f"negative discovery report row is not DN: {report_id}")
    for key in ("failed_gate", "what_was_learned"):
        if not _is_nonempty(item.get(key)):
            raise ValueError(f"negative discovery report row missing {key}: {report_id}")
    if not (_is_nonempty(item.get("next_hypothesis")) or _is_nonempty(item.get("stop_reason"))):
        raise ValueError(f"negative discovery report row needs next_hypothesis or stop_reason: {report_id}")
    if report_id == DIMENSION_MISMATCH_REPORT_ID:
        if item.get("report") != "dimension-mismatch-debt-transfer":
            raise ValueError("dimension mismatch DN report must keep source report identity")
        if item.get("base_level") != "D4":
            raise ValueError("dimension mismatch scale leakage DN report requires base_level D4")
        if item.get("effective_level") != "DN":
            raise ValueError("dimension mismatch scale leakage DN report requires effective_level DN")
        if item.get("terminal_verdict") != "negative_discovery":
            raise ValueError("dimension mismatch scale leakage DN report requires terminal_verdict negative_discovery")
        if item.get("failed_gate") != "$.dimension_mismatch_debt_transfer.anti_triviality_status":
            raise ValueError("dimension mismatch scale leakage DN report requires anti-triviality failed_gate")
        if item.get("anti_triviality_status") == "scale_leakage_detected" and item.get("effective_level") == "D4":
            raise ValueError("scale leakage cannot leave effective_level at D4")
        _validate_dimension_mismatch_scale_leakage_mapping(root, item)
    if report_id in DERIVATIVE_DN_REPORT_IDS:
        if item.get("report") != report_id:
            raise ValueError("derivative DN report must keep source report identity")
        if not _is_nonempty(item.get("debt_row_pointer")):
            raise ValueError("derivative DN report requires debt_row_pointer")
        artifact = str(item.get("json_artifact") or "")
        debt_pointer = item.get("debt_row_pointer")
        if not isinstance(debt_pointer, str) or resolve_artifact_pointer(root, f"{artifact}:{debt_pointer}") is None:
            raise ValueError("derivative DN report debt_row_pointer does not resolve")
    failed_gate = item.get("failed_gate")
    artifact = str(item.get("json_artifact") or "")
    if isinstance(failed_gate, str) and failed_gate.startswith("$."):
        pointer = f"{artifact}:{failed_gate}"
    elif isinstance(failed_gate, str) and ":$." in failed_gate:
        pointer = failed_gate
    else:
        pointer = str(item.get("ledger_pointer") or item.get("source") or "")
    if not pointer or resolve_artifact_pointer(root, pointer) is None:
        raise ValueError(f"negative discovery report failed_gate pointer does not resolve: {report_id}")
    if _is_anti_triviality_failure(item):
        _validate_anti_triviality_negative_boundary(root, item, pointer)
    if set(item) - OWNER_FACT_KEYS:
        extra = ", ".join(sorted(set(item) - OWNER_FACT_KEYS))
        raise ValueError(f"negative discovery report row has unsupported keys: {extra}")
    return item


def _is_anti_triviality_failure(item: Mapping[str, Any]) -> bool:
    failed_gate = item.get("failed_gate")
    if isinstance(failed_gate, str) and "anti_triviality" in failed_gate:
        return True
    if item.get("anti_triviality_status") not in (None, "pass", "anti_triviality_passed"):
        return True
    if item.get("downgrade_reason") in {
        "scale_only_or_metadata_proxy_sufficient",
        "metadata_proxy_sufficient",
        "anti_triviality_failed",
    }:
        return True
    return False


def _validate_anti_triviality_negative_boundary(
    root: Path,
    item: Mapping[str, Any],
    resolved_failed_gate_pointer: str,
) -> None:
    failed_gate = item.get("failed_gate")
    if not isinstance(failed_gate, str) or "anti_triviality" not in failed_gate:
        raise ValueError("anti-triviality DN report requires owner-local anti-triviality failed_gate")
    if item.get("base_level") not in POSITIVE_BASE_LEVELS:
        raise ValueError("anti-triviality DN report with positive base requires base_level")
    artifact = str(item.get("json_artifact") or "")
    if not resolved_failed_gate_pointer.startswith(f"{artifact}:"):
        raise ValueError("anti-triviality DN failed_gate must resolve inside the owner artifact")
    if resolve_artifact_pointer(root, resolved_failed_gate_pointer) in (None, "pass", "anti_triviality_passed"):
        raise ValueError("anti-triviality DN failed_gate does not resolve to a failing owner-local field")


def validate_negative_discovery_reports(
    root: Path,
    rows: Sequence[Mapping[str, Any]],
    *,
    require_required_ids: bool = True,
) -> list[dict[str, Any]]:
    validated: list[dict[str, Any]] = []
    for row in rows:
        report_id = _canonical_report_id(row)
        try:
            validated.append(validate_negative_report_row(root, row))
        except ValueError:
            if report_id in REQUIRED_NEGATIVE_REPORT_IDS:
                raise
            continue
    report_ids = {row["report_id"] for row in validated}
    if require_required_ids:
        missing = sorted(REQUIRED_NEGATIVE_REPORT_IDS - report_ids)
        if missing:
            raise ValueError(f"required negative discovery reports missing: {', '.join(missing)}")
    if len(report_ids) != len(validated):
        raise ValueError("duplicate negative discovery report ids")
    return validated


def _discovery_map_pointers_by_negative_id(root: Path) -> dict[str, str]:
    payload = load_validated_discovery_map_payload(root, artifact=DISCOVERY_MAP_ARTIFACT)
    raw_rows = payload.get("rows", [])
    rows = raw_rows if isinstance(raw_rows, list) else []
    result: dict[str, str] = {}
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            continue
        pointer = row.get("negative_report_pointer")
        if not isinstance(pointer, str):
            continue
        value = resolve_artifact_pointer(root, pointer)
        if isinstance(value, Mapping):
            negative_id = value.get("negative_id")
            if isinstance(negative_id, str):
                result[negative_id] = f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}].negative_report_pointer"
    return result


def build_negative_discovery_reports(
    *,
    root: Path,
    generated_at: str | None = None,
    discovery_rows: Sequence[Mapping[str, Any]],
    source_evidence: str = "backend_adapter.derive_negative_discovery_rows",
    require_required_ids: bool = True,
) -> dict[str, Any]:
    timestamp = _timestamp(generated_at)
    owner_rows = validate_negative_discovery_reports(root, list(discovery_rows), require_required_ids=require_required_ids)
    rows: list[dict[str, Any]] = []
    for row in owner_rows:
        source = str(row.get("source") or _source_from_map_row(row))
        item = dict(row)
        item.update(
            {
                "kind": "discovery_report",
                "source": source,
                "discovery_map_pointer": None,
                "ledger_pointer": source,
                "claim_verdict_pointer": None,
                "audit_status": "pass" if row.get("audit_status") == "pass" and resolve_artifact_pointer(root, source) is not None else "fail",
            }
        )
        rows.append(item)

    audit_reasons = [row["negative_id"] for row in rows if row["audit_status"] != "pass"]
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "status": "pointer-only",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "source_artifacts": {
            "source_evidence": source_evidence,
        },
        "row_count": len(rows),
        "audit_status": "pass" if not audit_reasons else "fail",
        "audit_reasons": audit_reasons,
        "rows": rows,
    }


def render_negative_reports_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Negative Discovery Reports",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Status: `{payload['status']}`",
        f"- Rows: `{payload['row_count']}`",
        "",
        "| negative id | report id | claim | failed gate | source | audit |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        lines.append(
            "| "
            f"`{row['negative_id']}` | "
            f"`{row['report_id']}` | "
            f"`{row['claim_id']}` | "
            f"`{row['failed_gate']}` | "
            f"`{row['source']}` | "
            f"`{row['audit_status']}` |"
        )
    lines.append("")
    return "\n".join(lines)


def write_negative_discovery_reports(
    *,
    root: Path,
    generated_at: str | None = None,
    discovery_rows: Sequence[Mapping[str, Any]],
    source_evidence: str = "backend_adapter.derive_negative_discovery_rows",
    require_required_ids: bool = True,
) -> dict[str, Any]:
    payload = build_negative_discovery_reports(
        root=root,
        generated_at=generated_at,
        discovery_rows=discovery_rows,
        source_evidence=source_evidence,
        require_required_ids=require_required_ids,
    )
    json_path = root / JSON_ARTIFACT
    markdown_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_negative_reports_markdown(payload), encoding="utf-8")
    return payload


def _verdicts_by_kind(rows: Sequence[Mapping[str, Any]]) -> dict[str, tuple[int, Mapping[str, Any]]]:
    result: dict[str, tuple[int, Mapping[str, Any]]] = {}
    for index, row in enumerate(rows):
        claim_id = row.get("claim_id")
        if isinstance(claim_id, str) and claim_id.startswith("claim:witness:"):
            result[claim_id.removeprefix("claim:witness:")] = (index, row)
    return result


def _verdicts_by_negative_report_pointer(rows: Sequence[Mapping[str, Any]]) -> dict[str, tuple[int, Mapping[str, Any]]]:
    result: dict[str, tuple[int, Mapping[str, Any]]] = {}
    for index, row in enumerate(rows):
        pointer = row.get("negative_report_pointer")
        if isinstance(pointer, str) and pointer:
            result[pointer] = (index, row)
    return result


def build_negative_witness_summary(
    *,
    root: Path,
    generated_at: str | None = None,
) -> dict[str, Any]:
    timestamp = _timestamp(generated_at)
    reports = _load_json(root, JSON_ARTIFACT)
    if not reports:
        raise ValueError("negative discovery reports must be written before witness summary")
    map_pointers = _discovery_map_pointers_by_negative_id(root)
    verdict_rows = _load_jsonl(root, CLAIM_VERDICTS_ARTIFACT)
    verdicts = _verdicts_by_kind(verdict_rows)
    negative_verdicts = _verdicts_by_negative_report_pointer(verdict_rows)
    witness_payload = _load_json(root, NEGATIVE_WITNESS_SUMMARY_ARTIFACT)
    raw_witnesses = witness_payload.get("witnesses", [])
    witnesses = raw_witnesses if isinstance(raw_witnesses, list) else []
    rows: list[dict[str, Any]] = []
    for index, row in enumerate(reports["rows"]):
        if row.get("kind") != "discovery_report":
            continue
        report_pointer = f"{JSON_ARTIFACT}:$.rows[{index}]"
        verdict_match = negative_verdicts.get(report_pointer)
        claim_verdict_pointer = None if verdict_match is None else f"{CLAIM_VERDICTS_ARTIFACT}:$.lines[{verdict_match[0]}]"
        reason_basis = reason_basis_from_negative_owner(row, claim_verdict_pointer=claim_verdict_pointer)
        reason = reason_for_claim_verdict(reason_basis)
        reason_drift = False
        if verdict_match is not None:
            try:
                validate_claim_verdict_reason(verdict_match[1], basis=reason_basis)
            except ValueError:
                reason_drift = True
        item = {
            "negative_id": row["negative_id"],
            "negative_verdict": "negative_discovery",
            "reason": reason,
            "ledger_pointer": row["ledger_pointer"],
            "discovery_map_pointer": row["discovery_map_pointer"],
            "witness_pointer": None,
            "claim_verdict_pointer": claim_verdict_pointer,
            "audit_status": row["audit_status"],
        }
        item["discovery_map_pointer"] = map_pointers.get(row["negative_id"])
        item["audit_status"] = (
            "pass"
            if item["discovery_map_pointer"] and verdict_match is not None and not reason_drift and row["audit_status"] == "pass"
            else "fail"
        )
        rows.append(item)
    for index, witness in enumerate(witnesses):
        if not isinstance(witness, Mapping):
            continue
        kind = str(witness.get("kind") or "")
        source = f"{NEGATIVE_WITNESS_SUMMARY_ARTIFACT}:$.witnesses[{index}]"
        match = verdicts.get(kind)
        claim = match[1] if match is not None else {}
        item = {
            "negative_id": f"witness:{kind}",
            "negative_verdict": str(claim.get("claim_verdict") or ""),
            "reason": str(claim.get("reason") or ""),
            "ledger_pointer": source,
            "discovery_map_pointer": None,
            "witness_pointer": source,
            "claim_verdict_pointer": None if match is None else f"{CLAIM_VERDICTS_ARTIFACT}:$.lines[{match[0]}]",
            "audit_status": "pass" if match is not None and kind and resolve_artifact_pointer(root, source) is not None else "fail",
        }
        rows.append(item)
    audit_reasons = [row["negative_id"] for row in rows if row["audit_status"] != "pass"]
    negative_ids = [row["negative_id"] for row in rows]
    duplicate_ids = sorted({negative_id for negative_id in negative_ids if negative_ids.count(negative_id) > 1})
    if duplicate_ids:
        raise ValueError(f"duplicate negative witness summary ids: {', '.join(duplicate_ids)}")
    dn_count = len(reports["rows"])
    witness_count = len(witnesses)
    return {
        "schema_id": SUMMARY_SCHEMA_ID,
        "artifact_id": SUMMARY_ARTIFACT_ID,
        "generated_at": timestamp,
        "status": "pointer-only",
        "json_artifact": SUMMARY_JSON_ARTIFACT,
        "markdown_artifact": SUMMARY_MARKDOWN_ARTIFACT,
        "source_artifacts": {
            "negative_discovery_reports": JSON_ARTIFACT,
            "claim_verdicts": CLAIM_VERDICTS_ARTIFACT,
        },
        "row_count": len(rows),
        "dn_discovery_map_row_count": dn_count,
        "witness_row_count": witness_count,
        "claim_verdict_row_count": len(verdict_rows),
        "audit_status": "pass" if not audit_reasons else "fail",
        "audit_reasons": audit_reasons,
        "rows": rows,
    }


def render_summary_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Discovery Negative Witness Summary",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Status: `{payload['status']}`",
        f"- Audit: `{payload['audit_status']}`",
        f"- Rows: `{payload['row_count']}`",
        "",
        "| negative id | verdict | reason | ledger | discovery map | witness | claim verdict | audit |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        lines.append(
            "| "
            f"`{row['negative_id']}` | "
            f"`{row['negative_verdict']}` | "
            f"`{row['reason']}` | "
            f"`{row['ledger_pointer']}` | "
            f"`{row['discovery_map_pointer']}` | "
            f"`{row['witness_pointer']}` | "
            f"`{row['claim_verdict_pointer']}` | "
            f"`{row['audit_status']}` |"
        )
    lines.append("")
    return "\n".join(lines)


def write_negative_witness_summary(*, root: Path, generated_at: str | None = None) -> dict[str, Any]:
    payload = build_negative_witness_summary(root=root, generated_at=generated_at)
    json_path = root / SUMMARY_JSON_ARTIFACT
    markdown_path = root / SUMMARY_MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_summary_markdown(payload), encoding="utf-8")
    return payload
