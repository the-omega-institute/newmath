#!/usr/bin/env python3
"""Validate the lab-local literature ledger pointer records."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
LEDGER_POINTER = "docs/lit/literature_ledger.yaml"
SCHEMA_ID = "bedc-quality-lab:literature-ledger"
REQUIRED_RECORD_COUNT = 6
REQUIRED_ROLES = (
    "evidence-envelope-reporting",
    "cost-protocol-quality-q",
    "gap-head-robustness-discovery-controls",
    "certificate-guided-negative-tradeoff",
    "formal-hardening-pointer-boundary",
    "artifact-release-navigation",
)
REQUIRED_RECORD_FIELDS = (
    "id",
    "pointer",
    "role",
    "used_by",
    "claim_boundary",
    "not_claimed",
    "revoke_if",
)
FORBIDDEN_POSITIVE_CLAIM_TERMS = (
    "full-lejepa",
    "global-quality",
    "full-tensor-namecert",
    "llm-behavior",
)
BEDC_BODY_MARKERS = (
    "\\closurestatus",
    "\\begin{closurestatus}",
    "\\origin{",
    "\\leanchecked",
    "\\leanvariant",
    "\\leansorryd",
    "\\leanstmt",
    "\\leandef",
    "\\theoryclosure",
    "\\scopeclosed",
    "\\formalstatus",
    "\\leantarget",
    "\\bridgestatus",
    "\\notclaimed",
    "\\upgradepath",
)
ALLOWED_LOCAL_PREFIXES = (
    "docs/",
    "reports/canonical/",
    "configs/",
    "bedc_quality_lab/",
    "tests/",
)
JSON_POINTER_RE = re.compile(
    r"^\$(?:\.[A-Za-z0-9_\-]+(?:\[(?:\*|\d+|[A-Za-z0-9_\-]+=[A-Za-z0-9_\-]+|\?\(@\.[A-Za-z0-9_\-]+==\"[^\"]+\"\))\])*)+$"
)
FILTER_RE = re.compile(r"^\?\(@\.([A-Za-z0-9_\-]+)==\"([^\"]+)\"\)$")
ROW_FILTER_RE = re.compile(r"^([A-Za-z0-9_\-]+)=([A-Za-z0-9_\-]+)$")


def validate_literature_ledger(root: Path | str = ROOT) -> dict[str, Any]:
    root_path = Path(root)
    ledger_path = root_path / LEDGER_POINTER
    failures: list[str] = []
    record_ids: list[str] = []
    role_hits: set[str] = set()
    records: list[Any] = []

    if not ledger_path.exists():
        return _summary(
            status="not-ready",
            record_count=0,
            record_ids=[],
            role_hits=set(),
            failures=[f"missing ledger file: {LEDGER_POINTER}"],
        )

    try:
        payload = json.loads(ledger_path.read_text(encoding="utf-8"))
    except Exception as exc:
        return _summary(
            status="not-ready",
            record_count=0,
            record_ids=[],
            role_hits=set(),
            failures=[f"ledger is not valid JSON-compatible YAML: {exc}"],
        )

    raw_text = ledger_path.read_text(encoding="utf-8")
    failures.extend(_forbidden_text_failures(raw_text, "ledger"))

    if not isinstance(payload, dict):
        failures.append("ledger root must be an object")
    else:
        if payload.get("schema_id") != SCHEMA_ID:
            failures.append(f"schema_id must be {SCHEMA_ID}")
        records = payload.get("records", [])
        if not isinstance(records, list):
            failures.append("records must be a list")
            records = []
        for field in ("status", "ready_when", "not_claimed", "revoke_if"):
            if field not in payload:
                failures.append(f"missing top-level field: {field}")

    if len(records) < REQUIRED_RECORD_COUNT:
        failures.append(f"records count {len(records)} is below required {REQUIRED_RECORD_COUNT}")

    seen_ids: set[str] = set()
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            failures.append(f"records[{index}] must be an object")
            continue
        record_id = record.get("id")
        if isinstance(record_id, str) and record_id:
            record_ids.append(record_id)
            if record_id in seen_ids:
                failures.append(f"duplicate record id: {record_id}")
            seen_ids.add(record_id)
        else:
            failures.append(f"records[{index}] missing stable id")
            record_id = f"records[{index}]"

        for field in REQUIRED_RECORD_FIELDS:
            if field not in record:
                failures.append(f"{record_id} missing required field: {field}")

        role = record.get("role")
        if isinstance(role, str):
            role_hits.add(role)
            if role not in REQUIRED_ROLES:
                failures.append(f"{record_id} has unknown role: {role}")
        else:
            failures.append(f"{record_id} role must be a string")

        for field in ("claim_boundary", "not_claimed", "revoke_if"):
            value = record.get(field)
            if not isinstance(value, str) or not value.strip():
                failures.append(f"{record_id} field {field} must be non-empty text")

        for pointer_field in ("pointer", "used_by"):
            failures.extend(_validate_pointer_field(root_path, record_id, pointer_field, record.get(pointer_field)))

    missing_roles = sorted(set(REQUIRED_ROLES) - role_hits)
    if missing_roles:
        failures.append("missing required role(s): " + ", ".join(missing_roles))

    return _summary(
        status="ready" if not failures else "not-ready",
        record_count=len(records),
        record_ids=record_ids,
        role_hits=role_hits,
        failures=failures,
    )


def _summary(
    *,
    status: str,
    record_count: int,
    record_ids: list[str],
    role_hits: set[str],
    failures: list[str],
) -> dict[str, Any]:
    return {
        "status": status,
        "pointer": LEDGER_POINTER,
        "record_count": record_count,
        "required_record_count": REQUIRED_RECORD_COUNT,
        "record_ids": sorted(record_ids),
        "required_roles": list(REQUIRED_ROLES),
        "failures": failures,
    }


def _forbidden_text_failures(text: str, label: str) -> list[str]:
    lowered = text.lower()
    failures = [
        f"{label} contains forbidden positive claim term: {term}"
        for term in FORBIDDEN_POSITIVE_CLAIM_TERMS
        if term in lowered
    ]
    for marker in BEDC_BODY_MARKERS:
        if marker.lower() in lowered:
            failures.append(f"{label} contains copied BEDC body marker: {marker}")
    return failures


def _validate_pointer_field(root: Path, record_id: str, field: str, value: Any) -> list[str]:
    failures: list[str] = []
    values = value if isinstance(value, list) else [value]
    if not values or any(not isinstance(item, str) or not item.strip() for item in values):
        return [f"{record_id} field {field} must contain non-empty pointer text"]
    for pointer in values:
        failures.extend(_validate_local_pointer(root, record_id, field, pointer))
    return failures


def _validate_local_pointer(root: Path, record_id: str, field: str, pointer: str) -> list[str]:
    path_text, json_pointer = _split_pointer(pointer)
    if not any(path_text.startswith(prefix) for prefix in ALLOWED_LOCAL_PREFIXES):
        return [f"{record_id} field {field} has non-local pointer: {pointer}"]
    path = root / path_text
    if not path.exists():
        return [f"{record_id} field {field} points to missing path: {path_text}"]
    if json_pointer is None:
        return []
    if path.suffix != ".json":
        return [f"{record_id} field {field} has JSON pointer on non-JSON path: {pointer}"]
    if not JSON_POINTER_RE.match(json_pointer):
        return [f"{record_id} field {field} has invalid JSON pointer: {pointer}"]
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return [f"{record_id} field {field} points to unreadable JSON: {path_text}: {exc}"]
    if not jsonpath_exists(payload, json_pointer):
        return [f"{record_id} field {field} JSON pointer is missing: {pointer}"]
    return []


def _split_pointer(pointer: str) -> tuple[str, str | None]:
    marker = ":$"
    if marker not in pointer:
        return pointer, None
    path_text, suffix = pointer.split(marker, 1)
    return path_text, "$" + suffix


def jsonpath_exists(data: object, pointer: str) -> bool:
    nodes = [data]
    for segment in split_jsonpath(pointer[2:]):
        if not segment:
            return False
        key_match = re.match(r"^([A-Za-z0-9_\-]+)", segment)
        if key_match:
            key = key_match.group(1)
            nodes = [node[key] for node in nodes if isinstance(node, dict) and key in node]
            selector_part = segment[len(key):]
        else:
            selector_part = segment
        if not nodes:
            return False
        for selector in re.findall(r"\[([^\]]+)\]", selector_part):
            next_nodes: list[object] = []
            if selector == "*":
                for node in nodes:
                    if isinstance(node, list):
                        next_nodes.extend(node)
            elif selector.isdigit():
                index = int(selector)
                for node in nodes:
                    if isinstance(node, list) and index < len(node):
                        next_nodes.append(node[index])
            else:
                filter_match = FILTER_RE.match(selector)
                if filter_match:
                    field, expected = filter_match.groups()
                    for node in nodes:
                        if isinstance(node, list):
                            next_nodes.extend(
                                item
                                for item in node
                                if isinstance(item, dict) and item.get(field) == expected
                            )
                elif row_match := ROW_FILTER_RE.match(selector):
                    field, expected = row_match.groups()
                    for node in nodes:
                        if isinstance(node, list):
                            next_nodes.extend(
                                item
                                for item in node
                                if isinstance(item, dict) and item.get(field) == expected
                            )
                else:
                    return False
            nodes = next_nodes
            if not nodes:
                return False
    return bool(nodes)


def split_jsonpath(path: str) -> list[str]:
    segments: list[str] = []
    current: list[str] = []
    bracket_depth = 0
    for char in path:
        if char == "." and bracket_depth == 0:
            segments.append("".join(current))
            current = []
            continue
        if char == "[":
            bracket_depth += 1
        elif char == "]" and bracket_depth > 0:
            bracket_depth -= 1
        current.append(char)
    segments.append("".join(current))
    return segments


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help="bedc-quality-lab root")
    args = parser.parse_args(argv)
    summary = validate_literature_ledger(Path(args.root))
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["status"] == "ready" else 1


if __name__ == "__main__":
    sys.exit(main())
