#!/usr/bin/env python3
"""Produce the fair L1 decision canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.fair_l1_decision import GENERATED_AT, build_payload, write_artifacts


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = build_payload(root=args.root, generated_at=args.generated_at)
    write_artifacts(payload, root=args.root, generated_at=args.generated_at)
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "status": payload["decision"]["status"],
                "ladder_state": payload["ladder_state_projection"]["state"],
                "failed_gate": payload["decision"]["failed_gate"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
