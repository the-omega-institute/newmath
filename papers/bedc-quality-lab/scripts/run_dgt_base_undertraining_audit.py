#!/usr/bin/env python3
"""Produce the DGT base-undertraining audit canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.dgt_base_undertraining_audit import GENERATED_AT, build_payload, write_artifacts


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = build_payload(root=args.root, generated_at=args.generated_at)
    write_artifacts(payload, root=args.root, generated_at=args.generated_at)
    audit = payload["base_undertraining_audit"]
    print(
        json.dumps(
            {
                "artifact_id": audit["artifact_id"],
                "verdict": audit["verdict"],
                "claim_action": audit["claim_action"],
                "comparison_count": len(audit["comparison_rows"]),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
