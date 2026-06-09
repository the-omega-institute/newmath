#!/usr/bin/env python3
"""Produce the DGT neural-module ablation canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.dgt_neural_ablation import GENERATED_AT, build_payload, write_artifacts


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    parser.add_argument("--requested-device", choices=("auto", "cpu", "mps"), default="auto")
    args = parser.parse_args(argv)
    payload = build_payload(generated_at=args.generated_at, requested_device=args.requested_device)
    write_artifacts(payload, root=args.root, generated_at=args.generated_at)
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "status": payload["nabl_hardgates"]["status"],
                "device": payload["training_protocol"]["resolved_device"],
                "arm_count": len(payload["module_registry"]),
                "claim_count": len(payload["component_causal_claims"]),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
