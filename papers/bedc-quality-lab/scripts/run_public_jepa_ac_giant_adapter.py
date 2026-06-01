#!/usr/bin/env python3
"""Run the public V-JEPA2-AC Giant adapter on the tiny BEDC-JEPA scope."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_jepa_baselines import write_public_jepa_ac_giant_adapter


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train-count", type=int, default=64)
    parser.add_argument("--test-count", type=int, default=64)
    parser.add_argument("--seed", type=int, default=6061)
    parser.add_argument("--batch-size", type=int, default=1)
    args = parser.parse_args()
    path = ROOT / "reports" / "bedc_jepa_public_ac_giant_adapter.json"
    write_public_jepa_ac_giant_adapter(
        path,
        train_count=args.train_count,
        test_count=args.test_count,
        seed=args.seed,
        batch_size=args.batch_size,
    )
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
