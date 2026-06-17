#!/usr/bin/env python3
"""Build a fillable external baseline native-metric result template."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_baseline_native_metric_contract import (  # noqa: E402
    write_public_baseline_native_metric_template,
)


def main() -> None:
    target = ROOT / "reports" / "bedc_jepa_public_baseline_native_metric_template.json"
    write_public_baseline_native_metric_template(target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
