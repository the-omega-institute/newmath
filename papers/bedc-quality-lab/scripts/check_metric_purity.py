#!/usr/bin/env python3
"""Run the lab-local metric purity audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.metric_purity import run_metric_purity_audit


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--targets", help="Path to metric purity target manifest.")
    parser.add_argument("--allowlist", help="Path to metric purity allowlist.")
    parser.add_argument("--json", dest="json_path", help="Write the audit JSON payload to PATH.")
    parser.add_argument(
        "--fail-on-allowlist-miss",
        action="store_true",
        help="Retained for explicit callers; stale allowlist rows always fail.",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = run_metric_purity_audit(ROOT, targets_path=args.targets, allowlist_path=args.allowlist)
    if args.json_path:
        path = Path(args.json_path)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if payload["status"] != "pass":
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
