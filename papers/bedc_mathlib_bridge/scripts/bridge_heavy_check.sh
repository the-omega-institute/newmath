#!/usr/bin/env bash
# Load-gated wrapper for the bridge's heavy `make check` (full mathlib lake build
# + 6 gates + negative tests). Runs ONLY when the host has spare capacity, with a
# single-flight lock and reduced parallelism + nice/ionice, so it never competes
# with the main BEDC lean/paper pipeline (which it otherwise starves — the bridge
# mathlib build pinned load to 40 and dropped lean to 0 Round SUCCESS during
# 2026-07-01 row verification; see feedback_bridge_verify_exitcode_and_lake).
#
# Usage: bridge_heavy_check.sh [<bridge_project_dir>]
#   default bridge dir: the script's own ../  (papers/bedc_mathlib_bridge).
# Env:
#   BEDC_BRIDGE_MAX_LOAD   (default 18)  — wait while load1 exceeds this.
#   BEDC_BRIDGE_WAIT_MAX_S (default 1800) — give up waiting after this long.
#   BEDC_BRIDGE_LAKE_JOBS  (default 2).
# Exit: 0 = make check passed; 75 = could not acquire lock / load never cleared
#       (EX_TEMPFAIL — caller should retry later, NOT treat as a gate failure);
#       other = make check's real rc.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BRIDGE_DIR="${1:-$(cd "$SCRIPT_DIR/.." && pwd)}"
MAX_LOAD="${BEDC_BRIDGE_MAX_LOAD:-18}"
WAIT_MAX="${BEDC_BRIDGE_WAIT_MAX_S:-1800}"
JOBS="${BEDC_BRIDGE_LAKE_JOBS:-2}"
LOCK="/tmp/.bedc-bridge-heavy.lock"

load1() { uptime | sed -E 's/.*averages?: ([0-9.]+).*/\1/' | cut -d. -f1; }

# Single-flight: never run two heavy bridge checks at once.
if command -v flock >/dev/null 2>&1; then
  exec 9>"$LOCK"
  if ! flock -n 9; then
    echo "[bridge-heavy] another heavy check holds the lock — skip (retry later)"; exit 75
  fi
else
  LOCK_DIR="${LOCK}.d"
  if ! mkdir "$LOCK_DIR" 2>/dev/null; then
    echo "[bridge-heavy] another heavy check holds the lock — skip (retry later)"; exit 75
  fi
  trap 'rmdir "$LOCK_DIR" 2>/dev/null || true' EXIT
fi

# Wait for a low-load window so we don't starve the main pipeline.
waited=0
while [ "$(load1)" -gt "$MAX_LOAD" ]; do
  if [ "$waited" -ge "$WAIT_MAX" ]; then
    echo "[bridge-heavy] load stayed > $MAX_LOAD for ${WAIT_MAX}s — defer"; exit 75
  fi
  echo "[bridge-heavy] load $(load1) > $MAX_LOAD — waiting 60s ($waited/${WAIT_MAX}s)"
  sleep 60; waited=$((waited + 60))
done

echo "[bridge-heavy] load $(load1) <= $MAX_LOAD — running make check (JOBS=$JOBS, nice)"
cd "$BRIDGE_DIR"
# IONICE may be unavailable on macOS; guard it.
IONICE=""; command -v ionice >/dev/null 2>&1 && IONICE="ionice -c2 -n7"
LAKE_JOBS="$JOBS" MAKEFLAGS="-j$JOBS" nice -n 10 $IONICE make check
rc=$?
echo "[bridge-heavy] make check rc=$rc"
# NOTE: rc=124 with every gate logged PASS is a timeout on the slow negative
# tests, not a gate failure — the caller must inspect the log's per-gate PASS
# lines (see feedback_bridge_verify_exitcode_and_lake), not trust rc alone.
exit $rc
