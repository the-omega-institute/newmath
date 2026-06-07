#!/usr/bin/env python3
"""Write the public JEPA-family baseline registry."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_jepa_baselines import (
    write_public_jepa_baseline_comparison,
    write_public_jepa_baseline_registry,
)


def main() -> None:
    path = ROOT / "reports" / "bedc_jepa_public_baseline_registry.json"
    write_public_jepa_baseline_registry(path)
    print(f"wrote {path.relative_to(ROOT)}")
    comparison_path = ROOT / "reports" / "bedc_jepa_public_baseline_comparison.json"
    write_public_jepa_baseline_comparison(comparison_path)
    print(f"wrote {comparison_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
