#!/usr/bin/env python3
"""Single-screen status view for the BEDC bedc-deep pipeline.

Prints to stdout: server status, BOARD breakdown, target lifecycle table,
failure_kind histogram, Stage 2 reject clusters, recent commits, supervisor
log tail. Runs read-only — no state mutation.

Refresh repeatedly with `watch -n 30 python3 tools/bedc-deep/dashboard.py`
or just rerun manually.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "state"
TARGETS_DIR = SCRIPT_DIR / "targets"
SUPERVISOR_LOG = STATE_DIR / "supervisor_logs" / "supervisor.log"
ORACLE_SERVER_URL = "http://localhost:8767"

sys.path.insert(0, str(SCRIPT_DIR))


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _safe_get_server() -> dict:
    try:
        with urllib.request.urlopen(f"{ORACLE_SERVER_URL}/status", timeout=3) as r:
            return json.loads(r.read().decode("utf-8"), strict=False)
    except Exception as exc:
        return {"_error": str(exc)}


def _git(args: list[str]) -> str:
    try:
        return subprocess.run(
            ["git", *args],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        ).stdout
    except Exception:
        return ""


def _section(title: str) -> str:
    bar = "─" * (len(title) + 4)
    return f"\n┌{bar}┐\n│  {title}  │\n└{bar}┘"


def render_server(s: dict) -> str:
    if "_error" in s:
        return f"  status: DOWN ({s['_error']})"
    diag = s.get("diagnosis", "?")
    busy = s.get("agents_busy", "?")
    cap = s.get("max_agents", "?")
    queue = s.get("queue_length", "?")
    completed = s.get("completed", "?")
    active_recent = len(s.get("active_recent_agents") or [])
    out = [
        f"  diagnosis: {diag}",
        f"  agents:    {busy}/{cap} busy   queue={queue}   completed={completed}",
        f"  recent agents (last 120s): {active_recent}",
    ]
    for k, v in (s.get("agents") or {}).items():
        out.append(f"    busy {k}: task={v.get('task_id','?')} elapsed={v.get('elapsed','?')}s")
    return "\n".join(out)


def render_board() -> str:
    from dispatch_bedc_target import parse_board
    targets = parse_board()
    total = len(targets)
    finished = 0
    in_progress = 0
    pending = 0
    for t in targets.values():
        if (STATE_DIR / f"{t.slug}.json").exists():
            finished += 1
        elif (STATE_DIR / t.slug / ".in_progress").exists():
            in_progress += 1
        else:
            pending += 1
    out = [
        f"  total: {total}   finished: {finished}   in_progress: {in_progress}   pending: {pending}",
    ]
    return "\n".join(out)


def render_target_table() -> str:
    from lifecycle import derive_failure_kind, decide_next_action
    rows: list[str] = []
    if not STATE_DIR.exists():
        return "  (no state files)"
    rows.append(f"  {'TARGET':<8} {'KIND':<28} {'ATTEMPTS':<10} {'NEXT':<14} TITLE")
    for f in sorted(STATE_DIR.glob("*.json")):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        kind = d.get("failure_kind") or derive_failure_kind(d)
        action = decide_next_action({**d, "failure_kind": kind})
        attempts = d.get("attempts", 1)
        rows.append(
            f"  {d.get('target_id','?'):<8} {kind:<28} {str(attempts):<10} {action:<14} {(d.get('title') or '')[:40]}"
        )
    return "\n".join(rows)


def render_histogram() -> str:
    from lifecycle import histogram, FAILURE_KINDS
    hist = histogram()
    if not hist:
        return "  (no completed targets)"
    width = max(len(k) for k in hist) if hist else 30
    out: list[str] = []
    total = sum(hist.values())
    for kind, n in sorted(hist.items(), key=lambda kv: -kv[1]):
        bar = "█" * min(40, n * 2)
        out.append(f"  {kind:<{width}}  {n:>3}  {bar}")
    success = hist.get("none", 0)
    skipped = hist.get("pre_flight_duplicate", 0) + hist.get("stage2_duplicate_content", 0)
    attempted = total - skipped
    out.append("")
    if attempted > 0:
        out.append(f"  success rate (excl. paper duplicates): {success}/{attempted}  ({100.0 * success / attempted:.0f}%)")
    else:
        out.append(f"  no genuine attempts yet (all {total} targets matched existing paper content)")
    return "\n".join(out)


def render_reject_clusters() -> str:
    if not TARGETS_DIR.exists():
        return "  (no targets dir)"
    counts: dict[str, int] = {}
    for f in TARGETS_DIR.glob("*/stage2_result.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if d.get("verdict") not in ("reject", "compile_failed"):
            continue
        for r in d.get("rejection_reasons") or []:
            r_low = (r or "").lower()
            cat = "other"
            m = re.search(r"item\s*(\d+)", r_low)
            if m:
                cat = f"item_{m.group(1)}"
            elif "build invariant" in r_low:
                cat = "build_invariant"
            elif "content duplication" in r_low:
                cat = "content_duplication"
            elif "non-latex" in r_low or "trailing" in r_low:
                cat = "non_latex_trailing"
            counts[cat] = counts.get(cat, 0) + 1
    if not counts:
        return "  (no Stage 2 rejects yet)"
    return "\n".join(
        f"  {k:<24}  {v:>3}  {'█' * min(40, v * 2)}"
        for k, v in sorted(counts.items(), key=lambda kv: -kv[1])
    )


def render_recent_commits(n: int = 5) -> str:
    out = _git(["log", "--oneline", f"-{n}"])
    return "\n".join(f"  {ln}" for ln in out.splitlines())


def render_supervisor_tail(n: int = 8) -> str:
    if not SUPERVISOR_LOG.exists():
        return "  (no supervisor log)"
    try:
        lines = SUPERVISOR_LOG.read_text(encoding="utf-8").splitlines()[-n:]
    except OSError:
        return "  (could not read supervisor log)"
    return "\n".join(f"  {ln}" for ln in lines) if lines else "  (empty)"


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC bedc-deep dashboard")
    parser.add_argument("--no-clear", action="store_true", help="Skip clearing the screen")
    args = parser.parse_args()

    if not args.no_clear and sys.stdout.isatty():
        sys.stdout.write("\x1b[2J\x1b[H")

    print(f"BEDC bedc-deep dashboard  •  {_now_iso()}")
    print(_section("Server (:8767)"))
    print(render_server(_safe_get_server()))
    print(_section("BOARD"))
    print(render_board())
    print(_section("Target lifecycle"))
    print(render_target_table())
    print(_section("failure_kind histogram"))
    print(render_histogram())
    print(_section("Stage 2 reject clusters"))
    print(render_reject_clusters())
    print(_section("Recent commits"))
    print(render_recent_commits())
    print(_section("Supervisor tail"))
    print(render_supervisor_tail())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
