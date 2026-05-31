#!/usr/bin/env python3
"""Run the gradient-trained BEDC-JEPA objective benchmark."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.torch_bedc_jepa import run_torch_bedc_jepa_benchmark


def main() -> None:
    summary = run_torch_bedc_jepa_benchmark()
    path = ROOT / "reports" / "bedc_jepa_torch_objective.json"
    path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
