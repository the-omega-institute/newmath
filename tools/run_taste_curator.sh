#!/usr/bin/env bash
set -u
LOG="${1:-$(git rev-parse --show-toplevel)/scripts/logs/taste_curator.log}"
PY="${PYTHON:-python3}"
SCRIPT="$(git rev-parse --show-toplevel)/tools/taste_curator.py"
BACKOFF=10
MAX_BACKOFF=600
while true; do
  echo "[supervisor] $(date -u +%FT%TZ) starting taste_curator.py" >> "$LOG"
  "$PY" "$SCRIPT" >> "$LOG" 2>&1
  rc=$?
  echo "[supervisor] $(date -u +%FT%TZ) taste_curator.py exited rc=$rc" >> "$LOG"
  if [ "$rc" -eq 0 ]; then BACKOFF=10; fi
  sleep "$BACKOFF"
  BACKOFF=$(( BACKOFF < MAX_BACKOFF ? BACKOFF * 2 : MAX_BACKOFF ))
done
