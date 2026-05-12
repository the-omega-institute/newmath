#!/usr/bin/env python3
"""Low-cadence bridge supervisor for Automath/NewMath intake.

This loop keeps the bridge from becoming a high-frequency production worker.
It refreshes a NewMath emergence index more often, and only runs full bridge
intake on a long cadence, defaulting to 12 hours.
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
OMEGA_ROOT = REPO_ROOT.parent
AUTOMATH_ROOT = OMEGA_ROOT / "automath"
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


def refresh_emergence(*, push: bool) -> dict[str, object]:
    cmd = [sys.executable, str(SCRIPT_DIR / "newmath_emergence_index.py"), "--commit"]
    if push:
        cmd.append("--push")
    return _run(cmd, cwd=REPO_ROOT, timeout=240)


def run_newmath_intake(*, push: bool) -> dict[str, object]:
    cmd = [
        sys.executable,
        str(SCRIPT_DIR / "bridge_supervisor.py"),
        "--once",
        "--allow-dirty",
        "--include-unchanged",
        "--update-state",
        "--no-auto-dev-sync",
        "--apply-bedc-board-ingest",
        "--commit-durable",
        "--scan-limit-per-rule",
        "30",
        "--limit-per-rule",
        "3",
    ]
    if push:
        cmd.extend(["--push-bridge-branch", "--push-bedc-branch"])
    return _run(cmd, cwd=REPO_ROOT, timeout=1200)


def run_automath_intake(*, push: bool) -> dict[str, object]:
    supervisor = AUTOMATH_ROOT / "tools" / "automath_newmath_bridge" / "bridge_supervisor.py"
    cmd = [
        sys.executable,
        str(supervisor),
        "--once",
        "--allow-dirty",
        "--include-unchanged",
        "--update-state",
        "--apply-automath-writeback",
        "--automath-writeback-background",
        "--commit-durable",
        "--scan-limit-per-rule",
        "30",
        "--limit-per-rule",
        "3",
    ]
    if push:
        cmd.append("--push-branch")
    return _run(cmd, cwd=AUTOMATH_ROOT, timeout=1200)


def bridge_pass(*, push: bool) -> dict[str, object]:
    emergence_before = refresh_emergence(push=push)
    newmath = run_newmath_intake(push=push)
    automath = run_automath_intake(push=push)
    emergence_after = refresh_emergence(push=push)
    return {
        "emergence_before": emergence_before,
        "newmath_intake": newmath,
        "automath_intake": automath,
        "emergence_after": emergence_after,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run low-cadence Automath/NewMath bridge intake")
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--push", action="store_true")
    parser.add_argument("--bridge-interval-seconds", type=int, default=43200)
    parser.add_argument("--emergence-interval-seconds", type=int, default=3600)
    parser.add_argument("--run-intake-immediately", action="store_true")
    args = parser.parse_args(argv)

    last_bridge = 0.0 if args.run_intake_immediately else time.monotonic()
    while True:
        if STOP_FILE.exists():
            _log({"event": "stop_file_seen", "path": str(STOP_FILE)})
            return 0
        if args.once:
            result = bridge_pass(push=args.push) if args.run_intake_immediately else {"emergence": refresh_emergence(push=args.push)}
            _log({"event": "once", "result": result})
            return 0
        now = time.monotonic()
        if now - last_bridge >= max(3600, args.bridge_interval_seconds):
            _log({"event": "bridge_intake_start", "interval_seconds": args.bridge_interval_seconds})
            _log({"event": "bridge_intake_done", "result": bridge_pass(push=args.push)})
            last_bridge = time.monotonic()
        else:
            _log({"event": "emergence_refresh", "result": refresh_emergence(push=args.push)})
        sleep_for = min(max(300, args.emergence_interval_seconds), max(300, args.bridge_interval_seconds))
        time.sleep(sleep_for)


if __name__ == "__main__":
    raise SystemExit(main())
