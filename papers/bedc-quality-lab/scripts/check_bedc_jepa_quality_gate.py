#!/usr/bin/env python3
"""Check the BEDC-JEPA tiny-world quality gate."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_quality_packet import check_bedc_jepa_quality_packet


def main() -> None:
    gate = check_bedc_jepa_quality_packet(ROOT / "reports" / "bedc_jepa_quality_packet.json")
    print(json.dumps(gate, indent=2, sort_keys=True))
    if gate["decision"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
