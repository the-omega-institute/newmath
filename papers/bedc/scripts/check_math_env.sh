#!/usr/bin/env bash
# Pre-build gate: forbidden math envs at top level.
#
# CLAUDE.md and the paper style require:
#   inline math:  $...$
#   display math: $$...$$  (each $$ on its own line)
#   multi-line displays: \begin{aligned}/\begin{gathered} INSIDE $$...$$
#
# Forbidden at top level:
#   \[ ... \]
#   \begin{equation}, \begin{equation*},
#   \begin{align},    \begin{align*},
#   \begin{eqnarray}, \begin{eqnarray*}
#
# This script is fail-fast: any violation prints file:line and exits 1.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

exec python3 - <<'PY'
import re, sys
from pathlib import Path

DIRS = ["parts", "frontmatter", "appendices"]
PATTERNS = [
    re.compile(r"\\begin\{align\*?\}"),
    re.compile(r"\\end\{align\*?\}"),
    re.compile(r"\\begin\{eqnarray\*?\}"),
    re.compile(r"\\end\{eqnarray\*?\}"),
    re.compile(r"\\begin\{equation\*?\}"),
    re.compile(r"\\end\{equation\*?\}"),
    re.compile(r"(?<!\\)\\\["),
    re.compile(r"(?<!\\)\\\]"),
]

hits = []
for d in DIRS:
    p = Path(d)
    if not p.is_dir():
        continue
    for tex in p.rglob("*.tex"):
        try:
            for i, line in enumerate(tex.read_text(encoding="utf-8").splitlines(), 1):
                if line.lstrip().startswith("%"):
                    continue
                for pat in PATTERNS:
                    if pat.search(line):
                        hits.append(f"{tex}:{i}: {line.strip()[:120]}")
                        break
        except Exception:
            continue

if hits:
    print("FORBIDDEN math env at top level (CLAUDE.md):", file=sys.stderr)
    for h in hits:
        print(f"  {h}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Fix: use $$\\begin{aligned}...\\end{aligned}$$ or $$\\begin{gathered}...\\end{gathered}$$", file=sys.stderr)
    print("inside $$...$$ display blocks. See CLAUDE.md '数学符号写法'.", file=sys.stderr)
    sys.exit(1)
PY
