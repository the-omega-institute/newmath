#!/usr/bin/env python3
"""Write the public JEPA-family baseline registry."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_jepa_baselines import (
    import_public_jepa_baseline_metrics_file,
    write_public_jepa_baseline_external_result,
    write_public_jepa_baseline_comparison,
    write_public_jepa_baseline_registry,
)


def main() -> None:
    path = ROOT / "reports" / "bedc_jepa_public_baseline_registry.json"
    write_public_jepa_baseline_registry(path)
    print(f"wrote {path.relative_to(ROOT)}")
    comparison_path = ROOT / "reports" / "bedc_jepa_public_baseline_comparison.json"
    external_path = ROOT / "reports" / "bedc_jepa_public_baseline_external_result.json"
    external_result = write_public_jepa_baseline_external_result(external_path)
    print(f"wrote {external_path.relative_to(ROOT)}")
    if external_result.get("status") == "available":
        import_public_jepa_baseline_metrics_file(external_path, comparison_path)
    else:
        write_public_jepa_baseline_comparison(comparison_path)
    print(f"wrote {comparison_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
