#!/usr/bin/env python3
"""Run the native public MiniGrid BEDC-JEPA benchmark packet."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_minigrid_native_benchmark import write_public_minigrid_native_benchmark


def main() -> None:
    target = ROOT / "reports" / "bedc_jepa_public_native_minigrid_benchmark.json"
    write_public_minigrid_native_benchmark(target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
