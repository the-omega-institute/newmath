#!/usr/bin/env python3
"""GPU concurrency backoff monitor + launch gate for the single-RTX-4090 box.

Two roles:
  monitor  poll nvidia-smi on an interval, append a CSV history line, and write
           a small JSON state file flagging GPU contention. Pure observability.
  gate     decide whether a new GPU job may launch right now: succeed (exit 0)
           when free memory and utilization headroom are sufficient, otherwise
           back off (exit 1), optionally waiting until headroom appears.

Reasoning codex (design-consensus / review / fix) are API-bound and do not touch
the GPU, so raising CODEX_FLOOR is safe; only torch experiment launches need to
consult `gate` before grabbing the card. stdlib only, no torch import.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time

# nvidia-smi is not on PATH inside this WSL2 shell; fall back to the WSL stub.
_SMI_CANDIDATES = ("nvidia-smi", "/usr/lib/wsl/lib/nvidia-smi")


def _resolve_smi() -> str | None:
    for cand in _SMI_CANDIDATES:
        found = shutil.which(cand) if os.path.sep not in cand else (cand if os.path.exists(cand) else None)
        if found:
            return found
    return None


def read_gpu() -> dict | None:
    """Return {util_pct, mem_used_mib, mem_total_mib, mem_free_mib} or None."""
    smi = _resolve_smi()
    if not smi:
        return None
    try:
        out = subprocess.run(
            [smi, "--query-gpu=utilization.gpu,memory.used,memory.total",
             "--format=csv,noheader,nounits"],
            capture_output=True, text=True, timeout=15,
        )
    except (subprocess.TimeoutExpired, OSError):
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    # First GPU line only (single-card box).
    first = out.stdout.strip().splitlines()[0]
    parts = [p.strip() for p in first.split(",")]
    if len(parts) < 3:
        return None
    try:
        util, used, total = int(float(parts[0])), int(float(parts[1])), int(float(parts[2]))
    except ValueError:
        return None
    return {
        "util_pct": util,
        "mem_used_mib": used,
        "mem_total_mib": total,
        "mem_free_mib": max(0, total - used),
    }


def has_headroom(snap: dict, *, need_mem_mib: int, max_util: int) -> bool:
    return snap["mem_free_mib"] >= need_mem_mib and snap["util_pct"] <= max_util


def cmd_gate(args) -> int:
    deadline = time.monotonic() + max(0, args.wait)
    while True:
        snap = read_gpu()
        if snap is None:
            # Fail open: if the GPU cannot be read, do not block the launch, but
            # say so loudly on stderr so the caller can notice a broken probe.
            print("gpu_backoff: nvidia-smi unavailable; failing open (allow launch)", file=sys.stderr)
            return 0
        if has_headroom(snap, need_mem_mib=args.need_mem_mib, max_util=args.max_util):
            print(f"OK util={snap['util_pct']}% free={snap['mem_free_mib']}MiB "
                  f"(need {args.need_mem_mib}MiB, max_util {args.max_util}%)")
            return 0
        if time.monotonic() >= deadline:
            print(f"BACKOFF util={snap['util_pct']}% free={snap['mem_free_mib']}MiB "
                  f"(need {args.need_mem_mib}MiB, max_util {args.max_util}%) — no headroom",
                  file=sys.stderr)
            return 1
        time.sleep(args.poll)


def cmd_monitor(args) -> int:
    state_path = args.state
    hist_path = args.history
    os.makedirs(os.path.dirname(state_path) or ".", exist_ok=True)
    contended_streak = 0
    while True:
        snap = read_gpu()
        ts = time.strftime("%Y-%m-%dT%H:%M:%S")
        if snap is None:
            state = {"ts": ts, "ok": False, "reason": "nvidia-smi unavailable"}
        else:
            contended = not has_headroom(snap, need_mem_mib=args.need_mem_mib, max_util=args.max_util)
            contended_streak = contended_streak + 1 if contended else 0
            state = {
                "ts": ts, "ok": True,
                **snap,
                "contended": contended,
                "contended_streak": contended_streak,
                "thresholds": {"need_mem_mib": args.need_mem_mib, "max_util": args.max_util},
            }
            if hist_path:
                try:
                    with open(hist_path, "a", encoding="utf-8") as fh:
                        fh.write(f"{ts},{snap['util_pct']},{snap['mem_used_mib']},"
                                 f"{snap['mem_free_mib']},{int(contended)}\n")
                except OSError:
                    pass
        tmp = state_path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(state, fh)
        os.replace(tmp, state_path)
        if args.once:
            print(json.dumps(state))
            return 0
        time.sleep(args.interval)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("gate", help="exit 0 if a GPU job may launch now, else exit 1")
    g.add_argument("--need-mem-mib", type=int, default=4000)
    g.add_argument("--max-util", type=int, default=80)
    g.add_argument("--wait", type=int, default=0, help="seconds to wait for headroom")
    g.add_argument("--poll", type=int, default=10)
    g.set_defaults(func=cmd_gate)

    m = sub.add_parser("monitor", help="poll nvidia-smi, log contention, write state")
    m.add_argument("--interval", type=int, default=30)
    m.add_argument("--need-mem-mib", type=int, default=4000)
    m.add_argument("--max-util", type=int, default=80)
    m.add_argument("--state", default="/tmp/gpu_backoff_state.json")
    m.add_argument("--history", default="/tmp/gpu_backoff_history.csv")
    m.add_argument("--once", action="store_true")
    m.set_defaults(func=cmd_monitor)

    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
