#!/usr/bin/env python3
"""Write the optional public MiniGrid adapter probe."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_minigrid_adapter import write_public_minigrid_probe


def main() -> None:
    path = ROOT / "reports" / "bedc_jepa_public_minigrid_probe.json"
    write_public_minigrid_probe(path)
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
