#!/usr/bin/env python3
"""Build near-native V-JEPA2-AC MiniGrid records."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.vjepa2_ac_near_native_reproduction import (  # noqa: E402
    write_vjepa2_ac_near_native_reproduction,
)


def main() -> None:
    reproduction_path = ROOT / "reports" / "bedc_vjepa2_ac_native_reproduction.json"
    comparison_path = ROOT / "reports" / "bedc_vjepa2_ac_native_readback_comparison.json"
    write_vjepa2_ac_near_native_reproduction(reproduction_path, comparison_path)
    print(f"wrote {reproduction_path.relative_to(ROOT)}")
    print(f"wrote {comparison_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
