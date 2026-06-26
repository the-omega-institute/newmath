#!/usr/bin/env python3
"""Build fail-closed public benchmark scope contracts."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.public_benchmark_scope_contracts import (  # noqa: E402
    write_public_benchmark_scope_contracts,
)


def main() -> None:
    target = ROOT / "reports" / "bedc_jepa_public_benchmark_scope_contracts.json"
    write_public_benchmark_scope_contracts(target)
    print(f"wrote {target.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
