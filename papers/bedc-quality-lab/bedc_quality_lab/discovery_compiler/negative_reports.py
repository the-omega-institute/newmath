"""Canonical negative discovery reports."""

from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .pointers import resolve_artifact_pointer


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


def _discovery_map_pointers_by_negative_id(root: Path) -> dict[str, str]:
    payload = _load_json(root, DISCOVERY_MAP_ARTIFACT)
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
) -> dict[str, Any]:
    timestamp = _timestamp(generated_at)
    owner_rows = list(discovery_rows)
    witness_payload = _load_json(root, NEGATIVE_WITNESS_SUMMARY_ARTIFACT)
    raw_witnesses = witness_payload.get("witnesses", [])
    witnesses = raw_witnesses if isinstance(raw_witnesses, list) else []

    rows: list[dict[str, Any]] = []
    for row in owner_rows:
        if not isinstance(row, Mapping) or row.get("discovery_level") != "DN":
            continue
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
    for index, witness in enumerate(witnesses):
        if not isinstance(witness, Mapping):
            continue
        kind = str(witness.get("kind") or "")
        source = f"{NEGATIVE_WITNESS_SUMMARY_ARTIFACT}:$.witnesses[{index}]"
        rows.append(
            {
                "negative_id": f"witness:{kind}",
                "kind": "witness",
                "source": source,
                "discovery_map_pointer": None,
                "ledger_pointer": source,
                "claim_verdict_pointer": None,
                "audit_status": "pass" if kind and resolve_artifact_pointer(root, source) is not None else "fail",
            }
        )

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
            "witnesses": NEGATIVE_WITNESS_SUMMARY_ARTIFACT,
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
        "| negative id | kind | source | audit |",
        "| --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        lines.append(f"| `{row['negative_id']}` | `{row['kind']}` | `{row['source']}` | `{row['audit_status']}` |")
    lines.append("")
    return "\n".join(lines)


def write_negative_discovery_reports(
    *,
    root: Path,
    generated_at: str | None = None,
    discovery_rows: Sequence[Mapping[str, Any]],
    source_evidence: str = "backend_adapter.derive_negative_discovery_rows",
) -> dict[str, Any]:
    payload = build_negative_discovery_reports(
        root=root,
        generated_at=generated_at,
        discovery_rows=discovery_rows,
        source_evidence=source_evidence,
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
    rows: list[dict[str, Any]] = []
    for index, row in enumerate(reports["rows"]):
        item = {
            "negative_id": row["negative_id"],
            "negative_verdict": "negative_discovery",
            "reason": "discovery-level-DN",
            "source": row["source"],
            "ledger_pointer": row["ledger_pointer"],
            "discovery_map_pointer": row["discovery_map_pointer"],
            "witness_pointer": None,
            "claim_verdict_pointer": None,
            "audit_status": row["audit_status"],
        }
        if row["kind"] == "discovery_report":
            item["discovery_map_pointer"] = map_pointers.get(row["negative_id"])
        if row["kind"] == "witness":
            kind = row["negative_id"].removeprefix("witness:")
            match = verdicts.get(kind)
            claim = match[1] if match is not None else {}
            item.update(
                {
                    "negative_verdict": str(claim.get("claim_verdict") or ""),
                    "reason": str(claim.get("reason") or ""),
                    "witness_pointer": row["source"],
                    "claim_verdict_pointer": None if match is None else f"{CLAIM_VERDICTS_ARTIFACT}:{match[0]}",
                    "audit_status": "pass" if match is not None and row["audit_status"] == "pass" else "fail",
                }
            )
        rows.append(item)
    audit_reasons = [row["negative_id"] for row in rows if row["audit_status"] != "pass"]
    dn_count = sum(1 for row in reports["rows"] if row["kind"] == "discovery_report")
    witness_count = sum(1 for row in reports["rows"] if row["kind"] == "witness")
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
