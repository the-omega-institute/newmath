#!/usr/bin/env bash
set -euo pipefail

# CI runs `make test` which regenerates .r110.ct first; we trust those files.
cd "$(dirname "$0")/.."

# Make sure 22 .algo.r110.ct files exist; regenerate via Makefile if missing.
if [ -x encoder/generate_r110_algo ]; then
    make >/dev/null 2>&1 || true  # ensure generator built
fi
for src in manifests/*/*.algo.ct; do
    out="${src%.algo.ct}.algo.r110.ct"
    if [ ! -f "$out" ]; then
        ./encoder/generate_r110_algo "$src" "$out" >/dev/null
    fi
done

LIMIT=52428800  # 50 MB — half of GitHub's 100 MB push limit. Real intent is
                # to catch periodic-segment unroll regressions (153 MB blowup).
fail=0
total=0
for f in manifests/*/*.algo.r110.ct; do
    total=$((total + 1))
    size=$(stat -f%z "$f" 2>/dev/null || stat -c%s "$f")
    if [ "$size" -gt "$LIMIT" ]; then
        echo "SIZE FAIL: $f = $size bytes (> $LIMIT)" >&2
        fail=$((fail + 1))
    fi
done

if [ "$fail" -gt 0 ]; then
    echo "FAIL: $fail / $total .algo.r110.ct files exceed 50 MB"
    exit 1
fi

echo "size guard OK: $total .algo.r110.ct files all under 50 MB"
