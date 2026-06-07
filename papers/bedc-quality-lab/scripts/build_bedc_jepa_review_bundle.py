#!/usr/bin/env python3
"""Build the BEDC-JEPA clean review bundle contract."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_review_bundle import write_review_bundle


def main() -> None:
    target = ROOT / "reports" / "bedc_jepa_review_bundle.json"
    write_review_bundle(target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
