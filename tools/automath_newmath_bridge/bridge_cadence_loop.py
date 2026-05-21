#!/usr/bin/env python3
"""Low-cadence bridge supervisor for Automath/NewMath landing search.

This loop keeps the bridge from becoming a high-frequency production worker.
Each pass refreshes source refs and emits NewMath landing-search knowledge
source entries. It does not write Automath material back, ingest BEDC BOARD
items, merge into BEDC branches, or commit runtime artifacts.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
STOP_FILE = SCRIPT_DIR / ".bridge_cadence_loop.stop"
LOG_FILE = SCRIPT_DIR / "logs" / "bridge_cadence_loop.log"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _log(payload: dict[str, object]) -> None:
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps({"created_at": _now_iso(), **payload}, ensure_ascii=False, sort_keys=True)
    print(line, flush=True)
    with LOG_FILE.open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _run(cmd: list[str], *, cwd: Path, timeout: int) -> dict[str, object]:
    started = time.monotonic()
    try:
        proc = subprocess.run(cmd, cwd=str(cwd), text=True, capture_output=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as exc:
        return {"status": "timeout", "cmd": cmd[:3], "timeout": timeout, "stdout": (exc.stdout or "")[-1000:], "stderr": (exc.stderr or "")[-1000:]}
    return {
        "status": "ok" if proc.returncode == 0 else "failed",
        "returncode": proc.returncode,
        "elapsed_seconds": round(time.monotonic() - started, 2),
        "stdout_tail": proc.stdout[-1500:],
        "stderr_tail": proc.stderr[-1500:],
    }


def run_landing_source_pass() -> dict[str, object]:
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_supervisor.py"),
        "--once",
        "--allow-dirty",
        "--include-unchanged",
        "--update-state",
        "--no-fetch",
        "--no-auto-dev-sync",
        "--no-bedc-board-ingest",
        "--no-merge-back-after-gates",
        "--scan-limit-per-rule",
        "30",
        "--limit-per-rule",
        "3",
    ]
    return _run(cmd, cwd=REPO_ROOT, timeout=1200)


def bridge_pass() -> dict[str, object]:
    landing_sources = run_landing_source_pass()
    return {
        "landing_source_pass": landing_sources,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run low-cadence Automath/NewMath landing-source bridge")
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--push", action="store_true", help="Accepted for old launch scripts; this loop does not push")
    parser.add_argument("--bridge-interval-seconds", type=int, default=43200)
    parser.add_argument("--idle-interval-seconds", type=int, default=3600)
    parser.add_argument("--run-intake-immediately", action="store_true")
    args = parser.parse_args(argv)
    if args.push:
        _log({"event": "push_ignored", "reason": "landing-source cadence does not commit or push runtime output"})

    last_bridge = 0.0 if args.run_intake_immediately else time.monotonic()
    while True:
        if STOP_FILE.exists():
            _log({"event": "stop_file_seen", "path": str(STOP_FILE)})
            return 0
        if args.once:
            result = bridge_pass() if args.run_intake_immediately else {"status": "idle_once"}
            _log({"event": "once", "result": result})
            return 0
        now = time.monotonic()
        if now - last_bridge >= max(3600, args.bridge_interval_seconds):
            _log({"event": "bridge_intake_start", "interval_seconds": args.bridge_interval_seconds})
            _log({"event": "bridge_intake_done", "result": bridge_pass()})
            last_bridge = time.monotonic()
        else:
            _log({"event": "idle", "seconds_until_next_bridge_pass": round(max(0.0, max(3600, args.bridge_interval_seconds) - (now - last_bridge)), 2)})
        sleep_for = min(max(300, args.idle_interval_seconds), max(300, args.bridge_interval_seconds))
        time.sleep(sleep_for)


if __name__ == "__main__":
    raise SystemExit(main())
