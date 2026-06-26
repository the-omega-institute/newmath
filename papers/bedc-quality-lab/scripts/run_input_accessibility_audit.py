#!/usr/bin/env python3
"""Produce the input-accessibility canonical audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.input_accessibility import GENERATED_AT, build_payload, extraction_failures, write_artifacts


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = build_payload(generated_at=args.generated_at)
    write_artifacts(payload, root=args.root)
    failures = extraction_failures(payload)
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "row_count": payload["row_count"],
                "access_gate_status": payload["access_hardgates"]["status"],
                "ood_gate_status": payload["ood_hardgates"]["status"],
                "boundary_ledger_count": len(payload["boundary_ledger"]),
                "registry_digest": payload["registry_digest"],
                "extraction_failure_count": len(failures),
            },
            sort_keys=True,
        )
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
