#!/usr/bin/env python3
"""Run BEDC-JEPA multistep latent-prediction evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_multistep_latent_prediction import (
    DEFAULT_SEEDS,
    run_bedc_multistep_latent_prediction,
)


def _parse_seeds(value: str) -> tuple[int, ...]:
    seeds = tuple(int(part.strip()) for part in value.split(",") if part.strip())
    if not seeds:
        raise argparse.ArgumentTypeError("at least one seed is required")
    return seeds


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=_parse_seeds, default=DEFAULT_SEEDS)
    parser.add_argument("--train-count", type=int, default=1536)
    parser.add_argument("--test-count", type=int, default=768)
    parser.add_argument("--epochs", type=int, default=220)
    parser.add_argument("--steps", type=int, default=3)
    parser.add_argument("--device", choices=("cuda", "auto", "cpu", "mps"), default="cuda")
    parser.add_argument("--output", type=Path, default=ROOT / "reports" / "bedc_multistep_latent_prediction.json")
    args = parser.parse_args()

    packet = run_bedc_multistep_latent_prediction(
        seeds=args.seeds,
        train_count=args.train_count,
        test_count=args.test_count,
        epochs=args.epochs,
        steps=args.steps,
        device=args.device,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    try:
        display_path = args.output.relative_to(ROOT)
    except ValueError:
        display_path = args.output
    print(f"wrote {display_path}")


if __name__ == "__main__":
    main()
