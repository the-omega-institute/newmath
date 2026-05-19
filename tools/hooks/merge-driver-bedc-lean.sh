#!/usr/bin/env bash
set -e
# Git merge driver: regenerate lean4/BEDC.lean from filesystem.
# Args: %O ancestor  %A current/output  %B other  %P path
test "$4" = "lean4/BEDC.lean"
repo="$(git rev-parse --show-toplevel)"
python3 "$repo/lean4/scripts/regenerate_bedc_lean.py" --root "$repo" --output "$2" >/dev/null
