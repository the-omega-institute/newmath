#!/usr/bin/env python3
"""Pre-build gate: parts/concrete_instances/ top-level .tex naming.

Files at parts/concrete_instances/*.tex (depth 1) must match:
    ^[0-9]+[a-z]?_[a-z][a-z0-9_]*\\.tex$

Examples (allowed): 04_nat_namecert_construction.tex, 35b_compact_image_total_bounded.tex
Examples (rejected): hilbert_orthogonal_projection_row.tex, 35B_caps.tex, _index.tex

Subdirectories (parts/concrete_instances/<theme>/...) are NOT checked. Other
theme directories (parts/core, parts/capstones, ...) are NOT checked.
"""
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
TARGET_DIR = ROOT / "parts" / "concrete_instances"
PATTERN = re.compile(r"^[0-9]+[a-z]?_[a-z][a-z0-9_]*\.tex$")


def main() -> int:
    if not TARGET_DIR.is_dir():
        print(f"missing dir: {TARGET_DIR}", file=sys.stderr)
        return 1

    bad = []
    for entry in sorted(TARGET_DIR.iterdir()):
        if not entry.is_file():
            continue
        if entry.suffix != ".tex":
            continue
        if not PATTERN.match(entry.name):
            bad.append(entry)

    if not bad:
        return 0

    print("BAD filename in parts/concrete_instances/ (must match ^[0-9]+[a-z]?_<concept>_*\\.tex$):", file=sys.stderr)
    for p in bad:
        print(f"  {p.relative_to(ROOT)}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Fix: rename to NN_<concept>_*.tex, or move to parts/concrete_instances/<theme>/ subdir.", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
