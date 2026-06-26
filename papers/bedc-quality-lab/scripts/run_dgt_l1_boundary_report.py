#!/usr/bin/env python3
"""Produce the DGT L1 boundary canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.dgt_l1_boundary_report import GENERATED_AT, build_l1_boundary_report, write_artifacts


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = build_l1_boundary_report(root=args.root, generated_at=args.generated_at)
    write_artifacts(payload, root=args.root, generated_at=args.generated_at)
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "artifact_role": payload["artifact_role"],
                "claim_promotion_eligible": payload["claim_promotion_eligible"],
                "scaling_claim_block": payload["scaling_claim_block"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
