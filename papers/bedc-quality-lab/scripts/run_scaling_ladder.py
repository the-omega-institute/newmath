#!/usr/bin/env python3
"""Produce the scaling-ladder canonical owner report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.scaling_ladder import (
    build_scaling_ladder_payload,
    write_artifacts,
)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at")
    args = parser.parse_args(argv)
    payload = build_scaling_ladder_payload(root=args.root, generated_at=args.generated_at)
    write_artifacts(payload, root=args.root)
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "schema_id": payload["schema_id"],
                "level_count": len(payload["levels"]),
                "boundary_count": len(payload["boundary_ledger"]),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
