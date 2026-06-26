#!/usr/bin/env python3
"""Produce the DGT component redundancy audit canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.dgt_component_redundancy_audit import GENERATED_AT, build_payload, write_artifacts


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = build_payload(root=args.root, generated_at=args.generated_at)
    write_artifacts(payload, root=args.root, generated_at=args.generated_at)
    audit = payload["component_redundancy_audit"]
    print(
        json.dumps(
            {
                "artifact_id": audit["artifact_id"],
                "audit_status": audit["audit_status"],
                "verdict_counts": audit["verdict_counts"],
                "global_recommendation": audit["global_recommendation"]["recommendation"],
                "component_count": len(audit["components"]),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
