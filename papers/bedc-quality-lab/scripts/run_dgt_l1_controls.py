#!/usr/bin/env python3
"""Produce the DGT L1 tiny-sequence control canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.dgt_l1_controls import GENERATED_AT, L1TrainingConfig, build_payload, write_artifacts


def _seed_tuple(text: str | None) -> tuple[int, ...] | None:
    if not text:
        return None
    return tuple(int(part) for part in text.split(",") if part.strip())


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    parser.add_argument("--requested-device", choices=("auto", "cpu", "mps"), default="cpu")
    parser.add_argument("--seeds", default=None, help="Comma-separated deterministic seeds; default uses the canonical eight seeds.")
    parser.add_argument("--training-steps", type=int, default=None)
    parser.add_argument("--train-examples", type=int, default=None)
    parser.add_argument("--eval-examples", type=int, default=None)
    args = parser.parse_args(argv)
    seed_override = _seed_tuple(args.seeds)
    config = L1TrainingConfig(
        seeds=seed_override if seed_override is not None else L1TrainingConfig().seeds,
        training_steps=args.training_steps if args.training_steps is not None else L1TrainingConfig().training_steps,
        train_examples=args.train_examples if args.train_examples is not None else L1TrainingConfig().train_examples,
        eval_examples=args.eval_examples if args.eval_examples is not None else L1TrainingConfig().eval_examples,
    )
    payload = build_payload(generated_at=args.generated_at, requested_device=args.requested_device, config=config)
    write_artifacts(payload, root=args.root, generated_at=args.generated_at)
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "status": payload["l1_tiny_sequence_projection"]["status"],
                "review_status": payload["review_status"],
                "promotion_readiness": payload["promotion_readiness"],
                "device": payload["training_arms"]["dgt_l1"]["device_resolved"],
                "compute_units": payload["compute_ledger"]["compute_units"],
                "opened_ladder_level": "L1_tiny_sequence",
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
