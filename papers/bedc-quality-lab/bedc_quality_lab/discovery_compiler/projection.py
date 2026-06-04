"""Generic projection helpers for backend-supplied discovery rows."""

from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .map import DISCOVERY_MAP_JSON_ARTIFACT, DISCOVERY_MAP_MARKDOWN_ARTIFACT, build_discovery_map_payload


def build_discovery_map(
    *,
    rows: Sequence[Mapping[str, Any]],
    generated_at: str | None = None,
    manifest_audit: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    return build_discovery_map_payload(rows=rows, generated_at=timestamp, manifest_audit=manifest_audit)


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
