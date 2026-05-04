#!/usr/bin/env bash
# Bidirectional auto-dev sync daemon: every INTERVAL seconds, run
# pull_from_auto_dev.py to converge our pipeline branch with the shared
# `auto-dev` integration branch (pull + push). Logs to
# scripts/logs/pull_daemon.log alongside loning's sync_daemon.log.
#
# Launch:
#   nohup ./tools/pull_from_auto_dev_daemon.sh > /dev/null 2>&1 &
#
# Tunables via env:
#   PULL_INTERVAL_SECONDS=600   (default)
#   PULL_LOCAL=bedc-claim-packet-pipeline
#   PULL_SHARED=auto-dev

set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOG_DIR="$REPO_ROOT/scripts/logs"
LOG_FILE="$LOG_DIR/pull_daemon.log"
SCRIPT="$REPO_ROOT/tools/pull_from_auto_dev.py"

INTERVAL="${PULL_INTERVAL_SECONDS:-600}"
LOCAL="${PULL_LOCAL:-bedc-claim-packet-pipeline}"
SHARED="${PULL_SHARED:-auto-dev}"

mkdir -p "$LOG_DIR"

echo "[daemon] starting auto-dev bidirectional sync daemon pid=$$ interval=${INTERVAL}s local=${LOCAL} shared=${SHARED}" \
  | tee -a "$LOG_FILE"

while true; do
  ts="$(date '+%Y-%m-%d %H:%M:%S')"
  echo "[daemon] $ts tick" >> "$LOG_FILE"
  python3 "$SCRIPT" --local "$LOCAL" --shared "$SHARED" >> "$LOG_FILE" 2>&1 \
    || echo "[daemon] $ts sync rc=$? (continuing)" >> "$LOG_FILE"
  sleep "$INTERVAL"
done
