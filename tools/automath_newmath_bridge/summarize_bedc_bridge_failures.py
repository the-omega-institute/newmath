#!/usr/bin/env python3
"""Summarize BEDC bridge-target failures without committing runtime logs.

The BEDC supervisor writes detailed state under `tools/bedc-deep/state/`.
That directory is runtime-only. This script extracts a small durable
source/destination/failure summary for bridge communication.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_BOARD = REPO_ROOT / "tools" / "bedc-deep" / "BOARD.completed.md"
DEFAULT_STATE = REPO_ROOT / "tools" / "bedc-deep" / "state"
DEFAULT_OUTPUT = REPO_ROOT / "docs" / "bridge" / "automath-newmath-failures.jsonl"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _iter_bridge_cursors(state_dir: Path) -> list[Path]:
    if not state_dir.exists():
        return []
    cursors: list[Path] = []
    for path in state_dir.glob("b-*/*cursor.json"):
        data = _read_json(path)
        text = json.dumps(data, ensure_ascii=False).lower()
        if "bridge" in text or "automath" in text or "s1" in text:
            cursors.append(path)
    return sorted(cursors)


def _target_id(path: Path) -> str:
    return path.parent.name.split("_", 1)[0].upper()


def _bridge_id(record: dict[str, Any]) -> str:
    payload = "|".join(
        str(record.get(key, ""))
        for key in ("source_repo", "source_branch_or_ref", "source_commit", "source_path", "target_id")
    )
    return hashlib.sha1(payload.encode("utf-8")).hexdigest()[:16]


def _record_from_cursor(path: Path) -> dict[str, Any] | None:
    data = _read_json(path)
    if not data:
        return None
    track = data.get("codex_track") if isinstance(data.get("codex_track"), dict) else {}
    last_failure = str(data.get("last_failure_kind") or track.get("last_failure_kind") or "")
    if not last_failure and str(track.get("verdict") or "") != "escalate":
        return None
    target_id = _target_id(path)
    record = {
        "schema_version": "automath-newmath-bridge-failure-v1",
        "created_at": _now_iso(),
        "bridge_direction": "automath_to_newmath",
        "source_repo": "the-omega-institute/automath",
        "source_branch_or_ref": "",
        "source_commit": "",
        "source_path": "",
        "source_artifact_kind": "lean_theorem",
        "destination_repo": "the-omega-institute/newmath",
        "destination_branch_or_ref": "bedc-claim-packet-pipeline",
        "destination_path": str(track.get("tex_file") or ""),
        "destination_artifact_kind": "audit_failure",
        "target_id": target_id,
        "status": "blocked",
        "failure_kind": last_failure or "bridge_escalated",
        "codex_verdict": str(track.get("verdict") or ""),
        "rounds_total": int(track.get("rounds_total") or 0),
        "operator_review_required": True,
        "taste_gate_required": False,
        "audit_required": True,
        "notes": "Summarized from BEDC runtime cursor; raw state/log files remain uncommitted.",
        "next_action": "Automath should treat this as blocked feedback until BEDC compile/audit passes or an operator resolves the target.",
    }
    record["bridge_id"] = _bridge_id(record)
    return record


def _existing_keys(path: Path) -> set[tuple[str, str]]:
    keys: set[tuple[str, str]] = set()
    if not path.exists():
        return keys
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict):
            keys.add((str(item.get("target_id", "")), str(item.get("failure_kind", ""))))
    return keys


def write_records(records: list[dict[str, Any]], output: Path) -> int:
    output.parent.mkdir(parents=True, exist_ok=True)
    keys = _existing_keys(output)
    wrote = 0
    with output.open("a", encoding="utf-8") as handle:
        for record in records:
            key = (str(record.get("target_id", "")), str(record.get("failure_kind", "")))
            if key in keys:
                continue
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
            keys.add(key)
            wrote += 1
    return wrote


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Summarize BEDC bridge failures into durable JSONL")
    parser.add_argument("--state-dir", default=str(DEFAULT_STATE))
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    args = parser.parse_args(argv)
    records = [record for path in _iter_bridge_cursors(Path(args.state_dir)) if (record := _record_from_cursor(path))]
    wrote = write_records(records, Path(args.output))
    print(json.dumps({"records": len(records), "written": wrote, "output": args.output}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
