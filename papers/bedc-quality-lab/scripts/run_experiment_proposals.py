#!/usr/bin/env python3
"""Write the experiment proposal pointer sidecar."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_compiler.experiment_proposals import write_experiment_proposals


def main() -> None:
    payload = write_experiment_proposals(ROOT)
    print(f"wrote {payload['row_count']} experiment proposals")


if __name__ == "__main__":
    main()
