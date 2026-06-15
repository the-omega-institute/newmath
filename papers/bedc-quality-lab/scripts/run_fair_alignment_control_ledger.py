#!/usr/bin/env python3
"""Write the canonical fair-alignment control ledger."""

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

from bedc_quality_lab.fair_alignment_control_ledger import (
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    build_payload,
    render_markdown,
)


def write_artifacts(*, root: Path = ROOT, generated_at: str | None = None) -> dict[str, object]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    payload = build_payload(generated_at=timestamp)
    json_path = root / JSON_ARTIFACT
    markdown_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=None)
    args = parser.parse_args(argv)
    payload = write_artifacts(root=args.root, generated_at=args.generated_at)
    print(json.dumps({"status": payload["status"], "rows": payload["row_count"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
