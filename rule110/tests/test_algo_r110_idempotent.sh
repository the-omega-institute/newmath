#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

GENERATOR="${GENERATOR:-./bin/generate_r110_algo}"
if [[ ! -x "$GENERATOR" ]]; then
  GENERATOR="./encoder/generate_r110_algo"
fi

if [[ ! -x "$GENERATOR" ]]; then
  echo "missing generator: ./bin/generate_r110_algo or ./encoder/generate_r110_algo" >&2
  exit 1
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/algo-r110-idempotent.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

count=0
while IFS= read -r manifest; do
  count=$((count + 1))
  stem="${manifest#manifests/}"
  stem="${stem%.algo.ct}"
  out_a="$TMP_DIR/${stem//\//__}.first.algo.r110.ct"
  out_b="$TMP_DIR/${stem//\//__}.second.algo.r110.ct"

  "$GENERATOR" "$manifest" "$out_a" >/dev/null
  "$GENERATOR" "$manifest" "$out_b" >/dev/null

  if ! diff -q -- "$out_a" "$out_b" >/dev/null; then
    echo "idempotency diff: $manifest" >&2
    diff -u -- "$out_a" "$out_b" >&2 || true
    exit 1
  fi
done < <(find manifests -mindepth 2 -maxdepth 2 -type f -name '*.algo.ct' | sort)

if [[ "$count" -eq 0 ]]; then
  echo "no .algo.ct manifests found" >&2
  exit 1
fi

echo "algo.r110.ct idempotency OK: $count manifest(s)"
