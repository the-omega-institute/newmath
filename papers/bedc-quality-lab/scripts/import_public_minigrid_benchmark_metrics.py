#!/usr/bin/env python3
"""Import externally executed public MiniGrid benchmark metrics."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_minigrid_adapter import import_public_minigrid_benchmark_metrics_file


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: python scripts/import_public_minigrid_benchmark_metrics.py <minigrid-result.json>")
    source = Path(sys.argv[1])
    target = ROOT / "reports" / "bedc_jepa_public_minigrid_benchmark_packet.json"
    import_public_minigrid_benchmark_metrics_file(source, target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
