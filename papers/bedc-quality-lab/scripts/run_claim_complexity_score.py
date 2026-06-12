#!/usr/bin/env python3
"""Write the pointer-only claim complexity canonical artifact."""

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

from bedc_quality_lab.claim_complexity import (
    build_claim_complexity_payload,
    render_claim_complexity_markdown,
    validate_claim_complexity_payload,
)


JSON_ARTIFACT = "reports/canonical/claim_complexity.json"
MARKDOWN_ARTIFACT = "reports/canonical/claim_complexity.md"


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def write_claim_complexity_score(*, root: Path | None = None, generated_at: str | None = None) -> dict:
    base = ROOT if root is None else root
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    payload = build_claim_complexity_payload(base, timestamp)
    errors = validate_claim_complexity_payload(base, payload)
    if errors:
        raise ValueError("; ".join(errors))
    _write_json(base / JSON_ARTIFACT, payload)
    _write_text(base / MARKDOWN_ARTIFACT, render_claim_complexity_markdown(payload))
    failing = [gate_id for gate_id, gate in payload["hardgates"].items() if gate.get("status") == "fail"]
    if failing:
        raise SystemExit(f"claim complexity hardgate failed: {', '.join(failing)}")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    parser.add_argument("--generated-at", default=None)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_claim_complexity_score(root=args.root, generated_at=args.generated_at)
    print(f"wrote {len(payload['rows'])} claim complexity rows to {JSON_ARTIFACT}")


if __name__ == "__main__":
    main()
