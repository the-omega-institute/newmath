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

from bedc_quality_lab.dgt_neural_ablation import (
    BASE_SEED,
    DgtNeuralAblationRunSpec,
    GENERATED_AT,
    build_payload,
    write_artifacts,
)


def _parse_steps(value: str) -> tuple[int, ...]:
    steps = tuple(int(part.strip()) for part in value.split(",") if part.strip())
    if not steps:
        raise argparse.ArgumentTypeError("at least one train step value is required")
    if any(step <= 0 for step in steps):
        raise argparse.ArgumentTypeError("train steps must be positive")
    return steps


def _parse_seeds(value: str) -> tuple[int, ...]:
    seeds = tuple(int(part.strip()) for part in value.split(",") if part.strip())
    if not seeds:
        raise argparse.ArgumentTypeError("at least one seed is required")
    return seeds


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    parser.add_argument("--requested-device", choices=("auto", "cpu", "mps"), default="auto")
    parser.add_argument("--train-steps", type=_parse_steps, default=(128, 256))
    parser.add_argument("--seed-count", type=int, default=8)
    parser.add_argument("--seeds", type=_parse_seeds, default=None)
    parser.add_argument("--quick-test", action="store_true", help="use a small non-canonical protocol for tests only")
    args = parser.parse_args(argv)
    if args.quick_test:
        run_spec = DgtNeuralAblationRunSpec.quick_test(requested_device=args.requested_device)
    else:
        seeds = args.seeds or tuple(BASE_SEED + index for index in range(args.seed_count))
        run_spec = DgtNeuralAblationRunSpec(
            step_grid=args.train_steps,
            seed_count=args.seed_count,
            seed_list=seeds,
            requested_device=args.requested_device,
            paired_ci_min_seeds=8,
        )
    payload = build_payload(generated_at=args.generated_at, requested_device=args.requested_device, run_spec=run_spec)
    write_artifacts(payload, root=args.root, generated_at=args.generated_at)
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "status": payload["nabl_hardgates"]["status"],
                "pure_status": payload["pure_hardgates"]["status"],
                "training_status": payload["training_protocol"]["status"],
                "stable_causal_attribution": payload["stable_causal_attribution"],
                "device": payload["training_protocol"]["resolved_device"],
                "step_grid": payload["training_protocol"].get("step_grid"),
                "seed_count": payload["training_protocol"].get("seed_count"),
                "arm_trainings": payload.get("compute_ledger", {}).get("training_matrix_count"),
                "arm_count": len(payload["module_registry"]),
                "claim_count": len(payload["component_causal_claims"]),
                "measured_claim_components": [row["component"] for row in payload["component_causal_claims"]],
                "scope_seal_scope_pressure_delta": payload.get("metric_delta_matrix", {})
                .get("DGT_without_scope_seal", {})
                .get("metrics", {})
                .get("scope_pressure_q"),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
