#!/usr/bin/env python3
"""Export a public JEPA-family baseline result boundary."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_jepa_baselines import write_public_jepa_baseline_external_result


def main() -> None:
    path = ROOT / "reports" / "bedc_jepa_public_baseline_external_result.json"
    write_public_jepa_baseline_external_result(path)
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
