#!/usr/bin/env python3
"""Produce and verify the pointer-only reproduction package."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.reproduction_package import (
    CHECK_RESULT_JSON_ARTIFACT,
    CHECK_RESULT_MARKDOWN_ARTIFACT,
    PACKAGE_JSON_ARTIFACT,
    PACKAGE_MARKDOWN_ARTIFACT,
    build_package,
    render_check_result_markdown,
    render_package_markdown,
    validate_package,
    verify_package,
)


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _load_package(root: Path) -> dict[str, object]:
    path = root / PACKAGE_JSON_ARTIFACT
    if not path.exists():
        raise FileNotFoundError(f"missing package artifact: {PACKAGE_JSON_ARTIFACT}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("package payload must be an object")
    return payload


def write_package(root: Path, generated_at: str) -> dict[str, object]:
    payload = build_package(root=root, generated_at=generated_at)
    _write_json(root / PACKAGE_JSON_ARTIFACT, payload)
    _write_text(root / PACKAGE_MARKDOWN_ARTIFACT, render_package_markdown(payload))
    return payload


def write_check_result(
    root: Path,
    *,
    profile: str,
    target_ids: Sequence[str],
    generated_at: str,
) -> dict[str, object]:
    package = _load_package(root)
    validate_package(package, root)
    payload = verify_package(
        package,
        root,
        profile=profile,  # type: ignore[arg-type]
        target_ids=target_ids,
        generated_at=generated_at,
    )
    _write_json(root / CHECK_RESULT_JSON_ARTIFACT, payload)
    _write_text(root / CHECK_RESULT_MARKDOWN_ARTIFACT, render_check_result_markdown(payload))
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--emit-package", action="store_true", help="Write the canonical package artifact.")
    parser.add_argument("--verify", action="store_true", help="Write a check-result artifact for a package profile.")
    parser.add_argument(
        "--profile",
        choices=("structural", "projection", "full-repro-ci"),
        default="structural",
    )
    parser.add_argument("--target", action="append", default=[], help="Restrict verification to one target id; repeatable.")
    parser.add_argument("--json-summary", action="store_true", help="Print the generated payload as JSON.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    generated_at = args.generated_at or datetime.now(timezone.utc).isoformat()
    payload: dict[str, object] | None = None
    if args.emit_package:
        payload = write_package(args.root, generated_at)
    if args.verify:
        payload = write_check_result(
            args.root,
            profile=args.profile,
            target_ids=tuple(args.target),
            generated_at=generated_at,
        )
    if payload is None:
        payload = write_package(args.root, generated_at)
    if args.json_summary:
        print(json.dumps(payload, sort_keys=True))
    failed_targets = payload.get("failed_targets")
    if isinstance(failed_targets, list) and failed_targets:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
