#!/usr/bin/env python3
"""Run the local BEDC-JEPA multi-step latent prediction smoke record."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_multistep_latent_prediction import run_multistep_latent_prediction_smoke


def main() -> None:
    packet = run_multistep_latent_prediction_smoke()
    path = ROOT / "reports" / "bedc_multistep_latent_prediction.json"
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
