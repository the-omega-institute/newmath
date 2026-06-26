#!/usr/bin/env python3
"""Run the four-system BEDC-JEPA boundary-world experiment."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_experiment import run_bedc_jepa_experiment


def run_experiment() -> dict[str, object]:
    return run_bedc_jepa_experiment()


def main() -> None:
    summary = run_experiment()
    report_dir = ROOT / "reports"
    report_dir.mkdir(parents=True, exist_ok=True)
    json_path = report_dir / "bedc_jepa_four_system_experiment.json"
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {json_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
