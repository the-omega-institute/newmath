#!/usr/bin/env python3
"""Write BEDC latent claim certificate records."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.latent_claim_certificate import write_latent_claim_certificate_artifacts


def main() -> None:
    paths = write_latent_claim_certificate_artifacts(ROOT / "reports")
    for path in paths:
        print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
