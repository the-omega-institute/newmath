#!/usr/bin/env python3
"""Build the public V-JEPA2 adapter comparison artifact."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_jepa_baselines import write_public_jepa_adapter_comparison


def main() -> None:
    target = ROOT / "reports" / "bedc_jepa_public_adapter_comparison.json"
    write_public_jepa_adapter_comparison(
        target,
        bedc_path=ROOT / "reports" / "bedc_jepa_torch_objective.json",
        structure_path=ROOT / "reports" / "bedc_jepa_public_structure_adapter.json",
        pretrained_path=ROOT / "reports" / "bedc_jepa_public_pretrained_vitb_adapter.json",
    )
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

