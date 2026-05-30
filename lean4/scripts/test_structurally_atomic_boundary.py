#!/usr/bin/env python3

from __future__ import annotations

import re
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
TOKEN = "Structurally" + "Atomic"
FORBIDDEN = re.compile(
    re.escape(TOKEN) + r"\.(nearest_siblings|worker|routing|public)|"
    r"(worker|routing|public)[A-Za-z0-9_.-]*" + re.escape(TOKEN)
)


def main() -> int:
    violations: list[str] = []
    for root in (REPO / "lean4", REPO / "tools"):
        for path in root.rglob("*"):
            if not path.is_file():
                continue
            if path.suffix not in {".lean", ".py", ".md", ".txt"}:
                continue
            rel = path.relative_to(REPO).as_posix()
            if rel == "lean4/scripts/test_structurally_atomic_boundary.py":
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            for lineno, line in enumerate(text.splitlines(), start=1):
                if FORBIDDEN.search(line):
                    violations.append(f"{rel}:{lineno}:{line.strip()}")
    assert not violations, "forbidden boundary usage:\n" + "\n".join(violations)
    print("OK: boundary token is not active public-boundary or worker-routing input")
    return 0


if __name__ == "__main__":
    sys.exit(main())
