#!/usr/bin/env python3
"""Write the STI owner-local admission artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import bedc_quality_lab.tasks.sti as sti


GENERATED_AT: str | None = None


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", metavar="ISO8601", help="Override the artifact timestamp.")
    parser.add_argument("--json-summary", metavar="PATH", help="Write a compact JSON summary.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = sti.write_artifacts(root=ROOT, generated_at=args.generated_at or GENERATED_AT)
    if args.json_summary:
        summary = {
            "artifact_id": payload["artifact_id"],
            "generated_at": payload["generated_at"],
            "verdict": payload["verdict"],
            "hardgate_status": payload["hardgate"]["status"],
        }
        Path(args.json_summary).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
