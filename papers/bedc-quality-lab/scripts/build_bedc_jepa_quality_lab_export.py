#!/usr/bin/env python3
"""Write the BEDC-JEPA quality-lab export registry."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_quality_lab_export import write_quality_lab_export


def main() -> None:
    target = ROOT / "reports" / "bedc_jepa_quality_lab_exports.json"
    write_quality_lab_export(target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
