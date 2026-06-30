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

from bedc_quality_lab.dgt_base_undertraining_audit import (
    FAIR_BASELINE_EPOCHS,
    FAIR_BASELINE_SEEDS,
    GENERATED_AT,
    build_payload,
    train_non_starved_fair_baseline,
    write_artifacts,
)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    parser.add_argument("--device", default="auto", choices=("auto", "cpu", "mps", "cuda"))
    args = parser.parse_args(argv)
    fair_baseline = train_non_starved_fair_baseline(
        root=args.root,
        requested_device=args.device,
        seeds=FAIR_BASELINE_SEEDS,
        epoch_count=FAIR_BASELINE_EPOCHS,
        generated_at=args.generated_at,
        progress=True,
    )
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
                "fair_baseline": {
                    "seed_count": fair_baseline["seed_count"],
                    "seeds": fair_baseline["training_config"]["seeds"],
                    "epoch_count": fair_baseline["training_config"]["epoch_count"],
                    "accuracy_mean": fair_baseline["metrics"]["accuracy_mean"],
                    "loss_start_mean": fair_baseline["metrics"]["loss_start_mean"],
                    "loss_end_mean": fair_baseline["metrics"]["loss_end_mean"],
                    "loss_decrease_mean": fair_baseline["metrics"]["loss_decrease_mean"],
                    "validation_loss_mean": fair_baseline["metrics"]["validation_loss_mean"],
                },
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
