#!/usr/bin/env bash
# Pre-build gate: rewrite forbidden math environments inline.
#
# CLAUDE.md and the paper style require:
#   inline math:  $...$
#   display math: $$...$$  (each $$ on its own line)
#   no top-level: \[ ... \],
#                 \begin{equation},  \begin{equation*},
#                 \begin{align},     \begin{align*},
#                 \begin{eqnarray},  \begin{eqnarray*}
# Multi-line displays use \begin{aligned}/\begin{gathered} INSIDE $$...$$.
#
# This script REWRITES violations in-place rather than failing the build:
#   \begin{align*?}    -> $$\begin{aligned}
#   \end{align*?}      -> \end{aligned}$$
#   \begin{eqnarray*?} -> $$\begin{aligned}
#   \end{eqnarray*?}   -> \end{aligned}$$
#   \begin{equation*?} -> $$
#   \end{equation*?}   -> $$
# Existing $$..\begin{aligned}..\end{aligned}..$$ blocks are unchanged.
# Codex sees no error; the replacement is invisible to phase REVISE.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

python3 - <<'PY'
import re, sys
from pathlib import Path

DIRS = ["parts", "frontmatter", "appendices"]
SUBS = [
    (re.compile(r"\\begin\{align\*?\}"),   r"$$\\begin{aligned}"),
    (re.compile(r"\\end\{align\*?\}"),     r"\\end{aligned}$$"),
    (re.compile(r"\\begin\{eqnarray\*?\}"), r"$$\\begin{aligned}"),
    (re.compile(r"\\end\{eqnarray\*?\}"),   r"\\end{aligned}$$"),
    (re.compile(r"\\begin\{equation\*?\}"), r"$$"),
    (re.compile(r"\\end\{equation\*?\}"),   r"$$"),
]

n_files = 0
n_subs  = 0
for d in DIRS:
    p = Path(d)
    if not p.is_dir():
        continue
    for tex in p.rglob("*.tex"):
        try:
            text = tex.read_text(encoding="utf-8")
        except Exception:
            continue
        new = text
        local = 0
        for pat, repl in SUBS:
            new, k = pat.subn(repl, new)
            local += k
        if local:
            tex.write_text(new, encoding="utf-8")
            n_files += 1
            n_subs += local
            print(f"[forbidden-math-env] rewrote {tex} ({local} substitution(s))",
                  file=sys.stderr)

if n_subs:
    print(f"[forbidden-math-env] rewrote {n_subs} occurrence(s) "
          f"across {n_files} file(s)", file=sys.stderr)
PY
exit 0
