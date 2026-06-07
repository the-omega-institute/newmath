#!/usr/bin/env python3
"""Write the BEDC-JEPA tiny-world quality packet."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_quality_packet import write_bedc_jepa_quality_packet


def main() -> None:
    write_bedc_jepa_quality_packet(ROOT / "reports")
    for name in (
        "bedc_jepa_quality_packet.json",
        "bedc_jepa_namecert.yaml",
        "bedc_jepa_gap_ledger.json",
        "bedc_jepa_quality_report.md",
    ):
        print(f"wrote {(ROOT / 'reports' / name).relative_to(ROOT)}")


if __name__ == "__main__":
    main()
