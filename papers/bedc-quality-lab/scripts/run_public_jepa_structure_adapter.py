#!/usr/bin/env python3
"""Run the public V-JEPA2 structure adapter on the tiny BEDC-JEPA scope."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_jepa_baselines import write_public_jepa_structure_adapter


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretrained", action="store_true")
    args = parser.parse_args()
    name = (
        "bedc_jepa_public_pretrained_vitb_adapter.json"
        if args.pretrained
        else "bedc_jepa_public_structure_adapter.json"
    )
    path = ROOT / "reports" / name
    write_public_jepa_structure_adapter(path, pretrained=args.pretrained)
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
