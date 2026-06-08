#!/usr/bin/env python3
"""Write the canonical model-comparison report and run-local owner artifacts."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.model_comparison import write_report


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", help="Stable timestamp for deterministic canonical regeneration.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_report(root=ROOT, generated_at=args.generated_at)
    print(f"wrote {payload['artifact_id']} {payload['status']}")


if __name__ == "__main__":
    main()
