#!/bin/sh
set -eu

cd "$(dirname "$0")/.."

limit=200000
count=0

for manifest in manifests/*/*.algo.r110.ct; do
  if [ ! -f "$manifest" ]; then
    echo "no .algo.r110.ct manifests found" >&2
    exit 1
  fi

  size=$(wc -c < "$manifest")
  count=$((count + 1))

  if [ "$size" -gt "$limit" ]; then
    echo "algo.r110.ct size guard failed: $manifest is $size bytes" >&2
    exit 1
  fi
done

echo "algo.r110.ct size guard OK: $count manifest(s)"
