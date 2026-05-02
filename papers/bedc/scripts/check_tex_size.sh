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
while IFS= read -r f; do
  n=$(wc -l < "$f")
  if [ "$n" -gt "$MAX" ]; then
    bad+="${f}: ${n} lines exceeds cap ${MAX}"$'\n'
  fi
done < <(find parts frontmatter appendices -name '*.tex' 2>/dev/null)

if [ -n "$bad" ]; then
  echo "OVERSIZED .TEX (cap ${MAX}) — split required, no PDF build:" >&2
  printf '%s' "$bad" >&2
  echo "" >&2
  echo "Fix: split each listed file at a natural section / theorem cluster" >&2
  echo "boundary into a sibling or child .tex under the same theme directory," >&2
  echo "wire the new \\input{...} into the parent file (or main.tex if the" >&2
  echo "parent is included from main.tex). Preserve all labels and markers." >&2
  echo "Then re-run make." >&2
  exit 1
fi
