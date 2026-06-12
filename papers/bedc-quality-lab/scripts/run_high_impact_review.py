#!/usr/bin/env python3
"""Write the high-impact review canonical artifact."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.high_impact_review import (
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    build_high_impact_review_payload,
    render_high_impact_review_markdown,
)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _reuse_index_generated_at(root: Path) -> str | None:
    path = root / "reports/canonical/index.json"
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    value = payload.get("generated_at") if isinstance(payload, Mapping) else None
    return value if isinstance(value, str) and value else None


def write_high_impact_review(*, root: Path = ROOT, generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at or _reuse_index_generated_at(root) or datetime.now(timezone.utc).isoformat()
    payload = build_high_impact_review_payload(root, generated_at=timestamp)
    _write_json(root / JSON_ARTIFACT, payload)
    markdown_path = root / MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_high_impact_review_markdown(payload), encoding="utf-8")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    write_high_impact_review(root=args.root, generated_at=args.generated_at)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
