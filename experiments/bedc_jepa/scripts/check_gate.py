#!/usr/bin/env python3
"""Check the BEDC-JEPA tiny world quality gate."""

from __future__ import annotations

import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.bedc_jepa.metrics.quality_gate import evaluate_quality_gate


def main() -> None:
    packet_path = ROOT / "experiments" / "bedc_jepa" / "reports" / "quality_packet.json"
    if not packet_path.exists():
        raise SystemExit("missing experiments/bedc_jepa/reports/quality_packet.json; run scripts/run_packet.py first")
    packet = json.loads(packet_path.read_text(encoding="utf-8"))
    gate = evaluate_quality_gate(packet)
    print(json.dumps(gate, indent=2, sort_keys=True))
    if gate["decision"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

