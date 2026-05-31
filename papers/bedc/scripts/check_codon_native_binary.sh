#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

TARGET="experiments/codon_window_spectra.py"
PATTERN='BASE_BITS|bits[[:space:]]*\([[:space:]]*codon[[:space:]]*\)|codon_from_bits|int[[:space:]]*\([[:space:]]*bits[[:space:]]*\(|sum[[:space:]]*\([[:space:]]*int[[:space:]]*\([[:space:]]*bits[[:space:]]*\('

if grep -nE "$PATTERN" "$TARGET" >&2; then
  echo "CODON native binary regression: bit-string substrate token in $TARGET" >&2
  exit 1
fi
