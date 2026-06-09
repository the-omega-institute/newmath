#!/usr/bin/env python3
"""Write the toy safety-boundary experiment artifacts."""

from __future__ import annotations

from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.toy_safety_boundary import validate_artifacts, write_artifacts


def main(argv: Sequence[str] | None = None) -> None:
    _ = argv
    write_artifacts(ROOT)
    validation = validate_artifacts(ROOT)
    if validation["status"] != "pass":
        raise SystemExit("; ".join(validation["errors"]))


if __name__ == "__main__":
    main()
