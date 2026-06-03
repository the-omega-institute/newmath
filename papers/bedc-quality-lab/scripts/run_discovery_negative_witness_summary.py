#!/usr/bin/env python3
"""Compile pointer-only negative witness summary rows."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_claim_verdict_demo import compile_claim_verdicts


SCHEMA_ID = "bedc-quality-lab:discovery-negative-witness-summary"
ARTIFACT_ID = "bedc-quality-lab:discovery-negative-witness-summary"
JSON_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.json"
MARKDOWN_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.md"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
NEGATIVE_WITNESSES_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
CLAIM_VERDICTS_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
ALLOWED_ROW_KEYS = frozenset(
    {
        "negative_id",
        "negative_verdict",
        "reason",
        "source",
        "ledger_pointer",
        "discovery_map_pointer",
        "witness_pointer",
        "claim_verdict_pointer",
        "audit_status",
    }
)


def _root(root: Path | None) -> Path:
    return ROOT if root is None else root


def _artifact_path(root: Path, artifact: str) -> Path:
    return root / artifact


def _read_json(root: Path, artifact: str) -> dict[str, Any]:
    path = _artifact_path(root, artifact)
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"source artifact must be a JSON object: {artifact}")
    return payload


def _json_pointer_value(root: Path, artifact_pointer: str | None) -> Any:
    if artifact_pointer is None or ":$." not in artifact_pointer:
        return None
    artifact, pointer = artifact_pointer.split(":", 1)
    path = _artifact_path(root, artifact)
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                if not isinstance(cursor, Mapping) or key not in cursor:
                    return None
                cursor = cursor[key]
            index_text = bracket[:-1]
            if not index_text.isdigit() or not isinstance(cursor, list):
                return None
            index = int(index_text)
            if index >= len(cursor):
                return None
            cursor = cursor[index]
            part = ""
        if not part:
            continue
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        else:
            return None
    return cursor


def _load_discovery_rows(root: Path) -> list[dict[str, Any]]:
    rows = _read_json(root, DISCOVERY_MAP_ARTIFACT).get("rows")
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        raise ValueError("discovery map source must expose $.rows[*]")
    return rows


def _load_witness_rows(root: Path) -> list[dict[str, Any]]:
    rows = _read_json(root, NEGATIVE_WITNESSES_ARTIFACT).get("witnesses")
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        raise ValueError("negative witness source must expose $.witnesses[*]")
    return rows


def _claim_verdict_rows(root: Path, generated_at: str | None) -> list[dict[str, Any]]:
    rows = compile_claim_verdicts(root, generated_at=generated_at)
    if not all(isinstance(row, dict) for row in rows):
        raise ValueError("compiled claim verdict rows must be JSON objects")
    return rows


def _dn_source(row: Mapping[str, Any]) -> str:
    pointer = row.get("failed_gate") or row.get("debt_row_pointer") or row.get("evidence_pointer")
    if not isinstance(pointer, str) or not pointer:
        return str(row["json_artifact"])
    return f"{row['json_artifact']}:{pointer}"


def _claim_verdict_pointer(line_index: int) -> str:
    return f"{CLAIM_VERDICTS_ARTIFACT}:{line_index}"


def _row(
    *,
    negative_id: str,
    negative_verdict: str,
    reason: str,
    source: str,
    ledger_pointer: str,
    discovery_map_pointer: str | None,
    witness_pointer: str | None,
    claim_verdict_pointer: str | None,
    audit_status: str,
) -> dict[str, Any]:
    item = {
        "negative_id": negative_id,
        "negative_verdict": negative_verdict,
        "reason": reason,
        "source": source,
        "ledger_pointer": ledger_pointer,
        "discovery_map_pointer": discovery_map_pointer,
        "witness_pointer": witness_pointer,
        "claim_verdict_pointer": claim_verdict_pointer,
        "audit_status": audit_status,
    }
    if frozenset(item) != ALLOWED_ROW_KEYS:
        raise ValueError(f"summary row has invalid keys: {sorted(item)}")
    return item


def _dn_rows(root: Path, discovery_rows: Sequence[Mapping[str, Any]], audit_reasons: list[str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, discovery in enumerate(discovery_rows):
        if discovery.get("discovery_level") != "DN":
            continue
        report = str(discovery.get("report", ""))
        negative_id = f"dn:{report}"
        source = _dn_source(discovery)
        audit_status = "pass" if report and _json_pointer_value(root, source) is not None else "fail"
        if negative_id in seen:
            audit_status = "fail"
            audit_reasons.append(f"duplicate DN discovery map row: {negative_id}")
        if not report:
            audit_reasons.append(f"DN discovery map row lacks report at index {index}")
        if audit_status == "fail":
            audit_reasons.append(f"DN source pointer does not resolve: {negative_id}")
        seen.add(negative_id)
        rows.append(
            _row(
                negative_id=negative_id,
                negative_verdict="negative_discovery",
                reason="discovery-level-DN",
                source=source,
                ledger_pointer=source,
                discovery_map_pointer=f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}]",
                witness_pointer=None,
                claim_verdict_pointer=None,
                audit_status=audit_status,
            )
        )
    return rows


def _verdicts_by_witness_kind(
    claim_rows: Sequence[Mapping[str, Any]],
    audit_reasons: list[str],
) -> dict[str, tuple[int, Mapping[str, Any]]]:
    matches: dict[str, list[tuple[int, Mapping[str, Any]]]] = {}
    for index, claim in enumerate(claim_rows):
        claim_id = claim.get("claim_id")
        if not isinstance(claim_id, str) or not claim_id.startswith("claim:witness:"):
            continue
        matches.setdefault(claim_id.removeprefix("claim:witness:"), []).append((index, claim))
    verdicts: dict[str, tuple[int, Mapping[str, Any]]] = {}
    for kind, kind_matches in matches.items():
        if len(kind_matches) != 1:
            audit_reasons.append(f"witness kind has {len(kind_matches)} compiled verdict rows: {kind}")
            continue
        verdicts[kind] = kind_matches[0]
    return verdicts


def _witness_rows(
    witness_rows: Sequence[Mapping[str, Any]],
    verdicts_by_kind: Mapping[str, tuple[int, Mapping[str, Any]]],
    audit_reasons: list[str],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, witness in enumerate(witness_rows):
        kind = str(witness.get("kind", ""))
        negative_id = f"witness:{kind}"
        witness_pointer = f"{NEGATIVE_WITNESSES_ARTIFACT}:$.witnesses[{index}]"
        verdict_match = verdicts_by_kind.get(kind)
        audit_status = "pass"
        if negative_id in seen:
            audit_status = "fail"
            audit_reasons.append(f"duplicate negative witness row: {negative_id}")
        if verdict_match is None:
            audit_status = "fail"
            audit_reasons.append(f"missing compiled witness verdict row: {negative_id}")
            claim_line = None
            claim = {}
        else:
            claim_line, claim = verdict_match
        verdict = str(claim.get("claim_verdict") or "")
        reason = str(claim.get("reason") or "")
        if not verdict or not reason:
            audit_status = "fail"
            audit_reasons.append(f"compiled witness verdict lacks verdict or reason: {negative_id}")
        seen.add(negative_id)
        rows.append(
            _row(
                negative_id=negative_id,
                negative_verdict=verdict,
                reason=reason,
                source=witness_pointer,
                ledger_pointer=witness_pointer,
                discovery_map_pointer=None,
                witness_pointer=witness_pointer,
                claim_verdict_pointer=None if claim_line is None else _claim_verdict_pointer(claim_line),
                audit_status=audit_status,
            )
        )
    return rows


def build_discovery_negative_witness_summary(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    base = _root(root)
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    audit_reasons: list[str] = []
    try:
        discovery_rows = _load_discovery_rows(base)
    except (FileNotFoundError, json.JSONDecodeError, ValueError) as exc:
        discovery_rows = []
        audit_reasons.append(f"missing or invalid source artifact: {DISCOVERY_MAP_ARTIFACT}: {exc}")
    try:
        witnesses = _load_witness_rows(base)
    except (FileNotFoundError, json.JSONDecodeError, ValueError) as exc:
        witnesses = []
        audit_reasons.append(f"missing or invalid source artifact: {NEGATIVE_WITNESSES_ARTIFACT}: {exc}")
    try:
        claim_rows = _claim_verdict_rows(base, generated_at=timestamp)
    except (FileNotFoundError, json.JSONDecodeError, ValueError) as exc:
        claim_rows = []
        audit_reasons.append(f"missing or invalid source artifact: {CLAIM_VERDICTS_ARTIFACT}: {exc}")
    rows = _dn_rows(base, discovery_rows, audit_reasons)
    rows.extend(_witness_rows(witnesses, _verdicts_by_witness_kind(claim_rows, audit_reasons), audit_reasons))
    dn_count = sum(1 for row in discovery_rows if row.get("discovery_level") == "DN")
    row_audit_failures = [row["negative_id"] for row in rows if row["audit_status"] != "pass"]
    audit_reasons.extend(f"row audit failed: {negative_id}" for negative_id in row_audit_failures)
    audit_status = "pass" if not audit_reasons and len(rows) == dn_count + len(witnesses) else "fail"
    if len(rows) != dn_count + len(witnesses):
        audit_reasons.append("summary row count does not match DN plus witness sources")
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "status": "pointer-only",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "source_artifacts": {
            "discovery_map": DISCOVERY_MAP_ARTIFACT,
            "negative_witnesses": NEGATIVE_WITNESSES_ARTIFACT,
            "claim_verdicts": CLAIM_VERDICTS_ARTIFACT,
        },
        "row_count": len(rows),
        "dn_discovery_map_row_count": dn_count,
        "witness_row_count": len(witnesses),
        "claim_verdict_row_count": len(claim_rows),
        "audit_status": audit_status,
        "audit_reasons": audit_reasons,
        "rows": rows,
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
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


def write_discovery_negative_witness_summary(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    base = _root(root)
    payload = build_discovery_negative_witness_summary(root=base, generated_at=generated_at)
    json_path = _artifact_path(base, JSON_ARTIFACT)
    markdown_path = _artifact_path(base, MARKDOWN_ARTIFACT)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_discovery_negative_witness_summary(root=args.root)
    print(f"wrote {payload['row_count']} negative witness summary rows to {JSON_ARTIFACT}")
    if payload["audit_status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
