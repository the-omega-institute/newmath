#!/usr/bin/env python3
"""Reject external bridge provenance leaked into BEDC paper body.

Automath / bridge records are allowed as review metadata and candidate
seeds. The BEDC paper body must re-derive accepted material natively and
must not cite those metadata paths as mathematical evidence.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


PAPER_DIR = Path(__file__).resolve().parents[1]
SCAN_ROOTS = [
    PAPER_DIR / "frontmatter",
    PAPER_DIR / "parts",
    PAPER_DIR / "appendices",
]

FORBIDDEN = [
    re.compile(r"Inspired by Omega Project"),
    re.compile(r"\b[Aa]utomath\b"),
    re.compile(r"automath/"),
    re.compile(r"discovery(?:\\_|\s*_)report\.json"),
    re.compile(r"tools[\\/]+automath_newmath_bridge[\\/]+review_packets[\\/]+[^}\s]+\.json"),
    re.compile(r"review_packets[\\/]+[^}\s]+\.json"),
]


def iter_tex_files() -> list[Path]:
    files: list[Path] = []
    for root in SCAN_ROOTS:
        if root.exists():
            files.extend(sorted(root.rglob("*.tex")))
    return files


def main() -> int:
    violations: list[str] = []
    for path in iter_tex_files():
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            violations.append(f"{path.relative_to(PAPER_DIR)}: read failed: {exc}")
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            for pattern in FORBIDDEN:
                if pattern.search(line):
                    rel = path.relative_to(PAPER_DIR)
                    violations.append(f"{rel}:{line_no}: external provenance leaked: {line.strip()[:220]}")
                    break

    if violations:
        print("External provenance check failed.", file=sys.stderr)
        print(
            "Automath / bridge / discovery JSON records are candidate metadata only; "
            "BEDC paper body must be re-derived natively.",
            file=sys.stderr,
        )
        for item in violations:
            print(item, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
