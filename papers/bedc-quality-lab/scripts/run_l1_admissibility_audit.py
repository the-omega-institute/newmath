#!/usr/bin/env python3
"""Produce the shared L1 admissibility audit canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.l1_admissibility_audit import DEFAULT_GENERATED_AT, write_artifacts


GENERATED_AT: str | None = DEFAULT_GENERATED_AT


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    parser.add_argument("--metrics-pointer", help="Artifact pointer to an owner-local canonical metrics object.")
    parser.add_argument("--json-summary", type=Path, help="Write a compact JSON summary.")
    args = parser.parse_args(argv)
    payload = write_artifacts(
        root=args.root,
        metrics_pointer=args.metrics_pointer,
        generated_at=args.generated_at,
    )
    summary = {
        "artifact_id": payload["artifact_id"],
        "status": payload["gate_card"]["status"],
        "failed_gate": payload["gate_card"]["failed_gate"],
    }
    if args.json_summary:
        args.json_summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    else:
        print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
