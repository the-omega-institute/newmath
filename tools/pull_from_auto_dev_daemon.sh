#!/usr/bin/env bash
# One-way pull daemon: every INTERVAL seconds, run pull_from_auto_dev.py
# to fast-forward / merge `origin/auto-dev` into our pipeline branch. Logs
# to scripts/logs/pull_daemon.log alongside loning's sync_daemon.log.
#
# Launch:
#   nohup ./tools/pull_from_auto_dev_daemon.sh > /dev/null 2>&1 &
#
# Tunables via env:
#   PULL_INTERVAL_SECONDS=600   (default)
#   PULL_TARGET=bedc-claim-packet-pipeline
#   PULL_UPSTREAM=auto-dev

set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOG_DIR="$REPO_ROOT/scripts/logs"
LOG_FILE="$LOG_DIR/pull_daemon.log"
SCRIPT="$REPO_ROOT/tools/pull_from_auto_dev.py"

INTERVAL="${PULL_INTERVAL_SECONDS:-600}"
TARGET="${PULL_TARGET:-bedc-claim-packet-pipeline}"
UPSTREAM="${PULL_UPSTREAM:-auto-dev}"

mkdir -p "$LOG_DIR"

echo "[daemon] starting pull_from_auto_dev daemon pid=$$ interval=${INTERVAL}s target=${TARGET} upstream=${UPSTREAM}" \
  | tee -a "$LOG_FILE"

while true; do
  ts="$(date '+%Y-%m-%d %H:%M:%S')"
  echo "[daemon] $ts tick" >> "$LOG_FILE"
  python3 "$SCRIPT" --target "$TARGET" --upstream "$UPSTREAM" >> "$LOG_FILE" 2>&1 \
    || echo "[daemon] $ts pull rc=$? (continuing)" >> "$LOG_FILE"
  sleep "$INTERVAL"
done
