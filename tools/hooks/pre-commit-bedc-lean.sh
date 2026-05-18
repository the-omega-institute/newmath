#!/usr/bin/env bash
set -e
# pre-commit hook: regenerate lean4/BEDC.lean if any staged file is under lean4/BEDC/
if git diff --cached --name-only | grep -qE '^lean4/BEDC/.*\.lean$'; then
  python3 "$(git rev-parse --show-toplevel)/lean4/scripts/regenerate_bedc_lean.py"
  git add "$(git rev-parse --show-toplevel)/lean4/BEDC.lean"
fi
exit 0
