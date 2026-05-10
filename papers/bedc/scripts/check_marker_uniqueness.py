#!/usr/bin/env python3
"""Pre-build gate: \\leanchecked{X} and \\leantarget{X} must be unique across paper body.

Each X is a paper-side claim with a Lean target. CLAUDE.md requires each X to
appear at exactly one canonical site (paper-claim primary). Variants of the same
claim use \\leanvariant{X} and are not subject to this uniqueness check.

Exception: markers inside `\\begin{closurestatus}...\\end{closurestatus}` blocks
are NOT counted -- closurestatus blocks are chapter-level metadata that legitimately
reference a Lean target as the formal evidence for a chapter's closure, and the
same Lean target may anchor closure in multiple chapters (e.g. an upstream namecert
cited by both its home chapter and a downstream chapter that depends on it).

Scans only .tex (not .md). Fails with file:line list of duplicates.
"""
import os
import re
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
TEX_DIRS = ["parts", "frontmatter", "appendices"]
MARKERS = ("leanchecked", "leantarget")


def main() -> int:
    sites: dict[tuple[str, str], list[tuple[Path, int]]] = defaultdict(list)
    for d in TEX_DIRS:
        base = ROOT / d
        if not base.is_dir():
            continue
        for tex in base.rglob("*.tex"):
            try:
                text = tex.read_text(encoding="utf-8")
            except Exception:
                continue
            in_closure = False
            for i, line in enumerate(text.splitlines(), 1):
                if line.lstrip().startswith("%"):
                    continue
                if "\\begin{closurestatus}" in line:
                    in_closure = True
                    continue
                if "\\end{closurestatus}" in line:
                    in_closure = False
                    continue
                if in_closure:
                    continue
                for kind in MARKERS:
                    for m in re.finditer(r"\\" + kind + r"\{([^}]+)\}", line):
                        sites[(kind, m.group(1))].append((tex, i))

    dups = [(k, v) for k, v in sites.items() if len(v) > 1]
    if not dups:
        return 0

    print("DUPLICATE \\leanchecked / \\leantarget X (paper-side primary site must be unique):", file=sys.stderr)
    for (kind, x), locs in sorted(dups):
        print(f"  \\{kind}{{{x}}}", file=sys.stderr)
        for p, ln in locs:
            rel = p.relative_to(ROOT)
            print(f"    {rel}:{ln}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Fix: keep one canonical site with \\leanchecked / \\leantarget, change others to \\leanvariant.", file=sys.stderr)
    print("(closurestatus blocks are exempt -- markers inside them are not counted.)", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
