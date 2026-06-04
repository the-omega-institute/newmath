#!/usr/bin/env python3
"""Build the canonical report discovery map."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.backends.current_lab import projection as _projection


_projection.ROOT = ROOT


if __name__ == "__main__":
    _projection.main()
else:
    sys.modules[__name__] = _projection
