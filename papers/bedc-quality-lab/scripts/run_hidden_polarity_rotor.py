#!/usr/bin/env python3
"""Write the Hidden-Polarity Rotor canonical artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import bedc_quality_lab.tasks.hidden_polarity_rotor as hpr


GENERATED_AT: str | None = None


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", metavar="ISO8601", help="Override the artifact timestamp.")
    parser.add_argument("--measured-result", metavar="PATH", help="Read an optional measured-result JSON intake.")
    parser.add_argument("--json-summary", metavar="PATH", help="Write a compact JSON summary.")
    return parser.parse_args(argv)


def _read_measured_result(path: str | None) -> dict[str, object] | None:
    if path is None:
        return None
    return json.loads(Path(path).read_text(encoding="utf-8"))


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    measured_result = _read_measured_result(args.measured_result)
    payload = hpr.write_artifacts(
        root=ROOT,
        generated_at=args.generated_at or GENERATED_AT,
        measured_result=measured_result,
    )
    if args.json_summary:
        summary = {
            "artifact_id": payload["artifact_id"],
            "generated_at": payload["generated_at"],
            "verdict": payload["verdict"],
            "hardgate_status": payload["hardgate"]["status"],
            "dependency_status": payload["dependency_status"]["status"],
        }
        Path(args.json_summary).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
