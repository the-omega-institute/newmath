#!/usr/bin/env bash
# Pre-build gate: forbidden math environments inside papers/bedc/.
# CLAUDE.md and the paper style require:
#   inline math:  $...$
#   display math: $$...$$  (each $$ on its own line)
#   no top-level: \[ ... \],
#                 \begin{equation}, \begin{equation*},
#                 \begin{align},    \begin{align*},
#                 \begin{eqnarray}, \begin{eqnarray*}
# Multi-line displays use \begin{aligned}/\begin{gathered} INSIDE $$...$$.
#
# Runs as part of `make` precheck, so codex sees the violations in the
# build output and fixes them in the same Phase REVISE iteration that
# introduced them.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

# Forbidden patterns. Pattern + a one-line replacement hint.
declare -a PATTERNS=(
  '\\begin\{equation\*?\}'
  '\\begin\{align\*?\}'
  '\\begin\{eqnarray\*?\}'
)

bad=""
for pat in "${PATTERNS[@]}"; do
  # grep -rn looks at every .tex file under parts/ frontmatter/ appendices/
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    bad+="$line"$'\n'
  done < <(grep -rEn "$pat" parts frontmatter appendices 2>/dev/null || true)
done

if [ -n "$bad" ]; then
  echo "[forbidden-math-env] gate failure: replace each violation with the \$\$...\$\$ form" >&2
  echo "$bad" >&2
  echo "" >&2
  echo "Replacement pattern:" >&2
  echo "  \\begin{align*}...\\end{align*}    -> \$\$\\begin{aligned}...\\end{aligned}\$\$" >&2
  echo "  \\begin{equation*}...\\end{equation*} -> \$\$...\$\$" >&2
  echo "  \\begin{equation}...\\end{equation}  -> \$\$...\$\$  (keep \\label outside if needed)" >&2
  echo "  \\begin{align}...\\end{align}      -> \$\$\\begin{aligned}...\\end{aligned}\$\$" >&2
  echo "  \\begin{eqnarray*}...\\end{eqnarray*} -> \$\$\\begin{aligned}...\\end{aligned}\$\$" >&2
  exit 1
fi
exit 0
