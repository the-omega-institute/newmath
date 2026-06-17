#!/usr/bin/env python3
"""Run a fixed-checkpoint V-JEPA2-AC MiniGrid latent-prediction evaluation."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.vjepa2_ac_latent_prediction import run_vjepa2_ac_minigrid_latent_prediction


def main() -> None:
    packet = run_vjepa2_ac_minigrid_latent_prediction()
    path = ROOT / "reports" / "bedc_vjepa2_ac_minigrid_latent_prediction.json"
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
