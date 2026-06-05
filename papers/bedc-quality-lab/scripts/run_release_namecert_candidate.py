#!/usr/bin/env python3
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.release_namecert_candidate import (
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    SIDECAR_PATH,
    SIDECAR_SCHEMA_ID,
    audit_release_namecert_candidate,
    build_release_namecert_candidate,
    render_release_namecert_candidate_markdown,
)


def write_release_namecert_candidate(
    *,
    root: Path,
    generated_at: str | None = None,
    make_check_passed: bool,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    sidecar_path = Path(root) / SIDECAR_PATH
    sidecar_payload, sidecar_digest = _load_sidecar(sidecar_path)
    candidate = build_release_namecert_candidate(
        sidecar_payload,
        sidecar_digest=sidecar_digest,
        generated_at=timestamp,
        make_check_passed=make_check_passed,
    )
    audit = audit_release_namecert_candidate(candidate)
    if audit["status"] != "pass":
        raise ValueError(f"release namecert candidate audit failed: {audit['failures']}")
    _write_json(Path(root) / JSON_ARTIFACT, candidate)
    _write_text(Path(root) / MARKDOWN_ARTIFACT, render_release_namecert_candidate_markdown(candidate))
    return candidate


def _load_sidecar(path: Path) -> tuple[dict[str, Any], str]:
    if not path.exists():
        raise ValueError(f"missing release manifest sidecar: {SIDECAR_PATH}")
    data = path.read_bytes()
    try:
        payload = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"malformed release manifest sidecar: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError("malformed release manifest sidecar: JSON root is not an object")
    _validate_sidecar_payload(payload)
    return payload, hashlib.sha256(data).hexdigest()


def _validate_sidecar_payload(payload: Mapping[str, Any]) -> None:
    if payload.get("schema_id") != SIDECAR_SCHEMA_ID:
        raise ValueError("release manifest sidecar schema mismatch")
    required_pointers = payload.get("required_pointers")
    if not isinstance(required_pointers, list) or not required_pointers:
        raise ValueError("release manifest sidecar lacks required pointers")
    unresolved = [
        row.get("id", "unknown")
        for row in required_pointers
        if not isinstance(row, Mapping) or row.get("status") != "resolved"
    ]
    if unresolved:
        raise ValueError(f"release manifest sidecar has unresolved required pointers: {unresolved}")
    revoke_if = payload.get("revoke_if")
    if not _nonempty_value(revoke_if):
        raise ValueError("release manifest sidecar lacks revoke_if")
    for key in (
        "artifact_id",
        "generated_at",
        "version",
        "release_bundle_status",
        "tag_status",
    ):
        if key not in payload:
            raise ValueError(f"release manifest sidecar lacks {key}")


def _nonempty_value(value: Any) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, dict)):
        return bool(value)
    return value is not None and bool(value)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _make_check_value(args: argparse.Namespace) -> bool:
    if args.make_check_passed:
        return True
    if args.make_check_failed:
        return False
    raise ValueError("pass explicit make-check evidence with --make-check-passed or --make-check-failed")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--generated-at", default=None)
    evidence = parser.add_mutually_exclusive_group()
    evidence.add_argument("--make-check-passed", action="store_true")
    evidence.add_argument("--make-check-failed", action="store_true")
    args = parser.parse_args()
    payload = write_release_namecert_candidate(
        root=Path(args.root),
        generated_at=args.generated_at,
        make_check_passed=_make_check_value(args),
    )
    print(payload["candidate_status"])


if __name__ == "__main__":
    main()
