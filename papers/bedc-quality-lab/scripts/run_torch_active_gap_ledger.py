#!/usr/bin/env python3
"""Run the torch OU active gap-ledger curriculum."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys

os.environ.setdefault("CUBLAS_WORKSPACE_CONFIG", ":4096:8")

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab import torch_bedc_jepa


def main() -> None:
    packet = torch_bedc_jepa.run_active_gap_ledger_curriculum()
    path = ROOT / "reports" / "bedc_jepa_active_gap_ledger.json"
    path.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
