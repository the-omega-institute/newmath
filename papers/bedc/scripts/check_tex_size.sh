#!/usr/bin/env bash
# Pre-build gate: any .tex file under papers/bedc/{parts,frontmatter,appendices}
# that exceeds MAX_TEX_LINES (CLAUDE.md hard cap) blocks the PDF build.
# Codex sees this in the make output and is expected to split the offending
# file at a natural section boundary (extract content into a sibling/child
# file under the same theme directory, leave the parent as a pure index of
# `\input{...}` lines), then re-run make.
set -euo pipefail

MAX=${MAX_TEX_LINES:-800}
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

bad=""
bad="$(MAX_TEX_LINES="$MAX" python3 - <<'PY'
import os
from pathlib import Path

max_lines = int(os.environ["MAX_TEX_LINES"])
roots = [Path("parts"), Path("frontmatter"), Path("appendices")]
for root in roots:
    if not root.exists():
        continue
    for path in root.rglob("*.tex"):
        if not path.is_file():
            continue
        with path.open("rb") as handle:
            line_count = sum(1 for _ in handle)
        if line_count > max_lines:
            print(f"{path}: {line_count} lines exceeds cap {max_lines}")
PY
)"

if [ -n "$bad" ]; then
  echo "OVERSIZED .TEX (cap ${MAX}) - split required, no PDF build:" >&2
  printf '%s' "$bad" >&2
  echo "" >&2
  echo "Fix: split each listed file at a natural section / theorem cluster" >&2
  echo "boundary into a sibling or child .tex under the same theme directory," >&2
  echo "wire the new \\input{...} into the parent file (or main.tex if the" >&2
  echo "parent is included from main.tex). Preserve all labels and markers." >&2
  echo "Then re-run make." >&2
  exit 1
fi
