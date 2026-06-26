#!/usr/bin/env python3
"""Build the fail-closed V-JEPA2-AC native reproduction boundary."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.vjepa2_ac_native_boundary import write_vjepa2_ac_native_boundary


def main() -> None:
    target = ROOT / "reports" / "bedc_jepa_vjepa2_ac_native_boundary.json"
    write_vjepa2_ac_native_boundary(target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
