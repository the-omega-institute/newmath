#!/usr/bin/env python3
"""Write the BEDC-JEPA external run kit contract."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_external_run_kit import write_external_run_kit


def main() -> None:
    path = ROOT / "reports" / "bedc_jepa_external_run_kit.json"
    write_external_run_kit(path)
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
