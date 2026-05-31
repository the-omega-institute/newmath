#!/usr/bin/env python3

from __future__ import annotations

import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
TOKEN = "Structurally" + "Atomic"
EXEMPT_REL_PATHS = {
    "lean4/scripts/test_structurally_atomic_boundary.py": "self token-split sentinel",
}
SOURCE_SUFFIXES = {".lean", ".py", ".md", ".txt", ".yml", ".yaml", ".sh"}


def main() -> int:
    violations: list[str] = []
    for root in (REPO / "lean4", REPO / "tools"):
        for path in root.rglob("*"):
            if not path.is_file():
                continue
            if path.suffix not in SOURCE_SUFFIXES:
                continue
            rel = path.relative_to(REPO).as_posix()
            if rel in EXEMPT_REL_PATHS:
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            for lineno, line in enumerate(text.splitlines(), start=1):
                if TOKEN in line:
                    violations.append(f"{rel}:{lineno}:{line.strip()}")
    assert not violations, "forbidden boundary usage:\n" + "\n".join(violations)
    print("OK: boundary token is absent from lean4/tools source")
    return 0


if __name__ == "__main__":
    sys.exit(main())
