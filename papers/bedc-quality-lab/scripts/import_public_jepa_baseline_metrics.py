#!/usr/bin/env python3
"""Import executed public JEPA-family baseline metrics into the comparison packet."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_jepa_baselines import import_public_jepa_baseline_metrics_file


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>")
    source = Path(sys.argv[1])
    target = ROOT / "reports" / "bedc_jepa_public_baseline_comparison.json"
    import_public_jepa_baseline_metrics_file(source, target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
