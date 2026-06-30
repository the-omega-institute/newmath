#!/usr/bin/env bash
# Claude Code statusline for the window-codon-bridge pipeline.
# Reports OUR daemon (launchctl window.codon.bridge.supervisor), claim verdict
# mix, active codex workers, last-cycle age, and ahead-of-origin count.
# Self-gates: fires when cwd is inside the window-bridge worktree, OR when cwd
# is the main newmath tree AND our daemon is running (so it takes over the bar
# whenever the window-bridge pipeline is the active one; otherwise it prints
# empty and the dispatch falls through to the next statusline).
# Claude Code passes session info on stdin as JSON.

set -e

WT="/Users/lexa/Desktop/lexa/omega/newmath-window-bridge"
MAIN="/Users/lexa/Desktop/lexa/omega/newmath"

INPUT=$(cat 2>/dev/null || true)

CWD=""
if [ -n "$INPUT" ]; then
  CWD=$(printf '%s' "$INPUT" | /usr/bin/python3 -c 'import json,sys
try:
  d=json.load(sys.stdin)
  print((d.get("workspace") or {}).get("current_dir") or d.get("cwd") or "")
except Exception:
  pass' 2>/dev/null || true)
fi

# Daemon PID (machine-global launchctl service, not cwd-dependent).
DAEMON_PID=$(ps aux | grep "window_codon_bridge/supervisor.py" | grep -v grep | awk '{print $2}' | head -1)

# Self-gate.
case "$CWD" in
  "$WT"*) ;;                                  # inside the worktree -> always fire
  "$MAIN")                                    # main tree -> fire only if our daemon is up
    [ -n "$DAEMON_PID" ] || exit 0 ;;
  "$MAIN"/*)
    [ -n "$DAEMON_PID" ] || exit 0 ;;
  *) exit 0 ;;
esac

BRANCH=$(cd "$WT" 2>/dev/null && git symbolic-ref --short HEAD 2>/dev/null || echo "?")
PROJECT="wcbridge/$BRANCH"

if [ -n "$DAEMON_PID" ]; then
  DAEMON_ETIME=$(ps -o etime= -p "$DAEMON_PID" 2>/dev/null | tr -d ' ')
  DAEMON="🟢 daemon:$DAEMON_PID ($DAEMON_ETIME)"
else
  DAEMON="🔴 daemon:OFF"
fi

# Active codex workers (machine-global).
CODEX_ACTIVE=$(ps aux | grep -E "codex exec" | grep -v grep | wc -l | tr -d ' ')

# Claim verdict mix.
CLAIMS_FILE="$WT/tools/window_codon_bridge/registries/claims.json"
CLAIMS_LINE="claims:?"
if [ -f "$CLAIMS_FILE" ]; then
  CLAIMS_LINE=$(/usr/bin/python3 -c "
import json
from collections import Counter
try:
    d = json.load(open('$CLAIMS_FILE'))
    cl = d['claims'] if isinstance(d, dict) else d
    c = Counter(x.get('status','?') for x in cl)
    print(f\"claims:{len(cl)} C{c.get('certified',0)}/X{c.get('coincidence',0)}/R{c.get('refuted',0)}/N{c.get('needs_external',0)}/O{c.get('open',0)}\")
except Exception:
    print('claims:?')
")
fi

# Last-cycle age (minutes since the daemon last wrote a cycle line).
LOG="$WT/tools/window_codon_bridge/state/daemon.stdout.log"
CYCLE="cycle:?"
if [ -f "$LOG" ]; then
  NOW=$(date +%s)
  MT=$(stat -f %m "$LOG" 2>/dev/null || echo "$NOW")
  AGE_MIN=$(( (NOW - MT) / 60 ))
  CYCLE="cycle:${AGE_MIN}m"
fi

# Sync state vs origin (worktree branch).
AHEAD=$(cd "$WT" 2>/dev/null && git rev-list --count origin/feat/window-codon-bridge..HEAD 2>/dev/null || echo "?")

echo "[$PROJECT] $DAEMON | codex_now:$CODEX_ACTIVE | $CLAIMS_LINE | $CYCLE | ahead:$AHEAD"
