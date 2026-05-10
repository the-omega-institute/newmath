#!/usr/bin/env python3
"""Daily AI growth pipeline status report.

Runs from cron / launchd / hand. Aggregates:
  - critical_path metadata (closed / open / drift / bridge / formal)
  - paper round + lean round throughput last 24h
  - ai chapter count and grades
  - gate-fail rate (audit / axiom-purity / conservativity / lake)
  - recovery success rate
  - chapters stuck in recovery > 12h
  - top-3 critical_path chapters
  - any prompt changes since yesterday's report

Output: stdout markdown. Operator reads.
"""

from __future__ import annotations
import json
import re
import subprocess
import sys
from collections import Counter
from datetime import datetime, timedelta
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
PAPER_LOG = REPO / "papers/bedc/scripts/logs/orchestrator.log"
LEAN_LOG = REPO / "lean4/scripts/logs/orchestrator.log"
SYNC_LOG = REPO / "scripts/logs/sync_daemon.log"


def _run(*args: str) -> str:
    return subprocess.run(args, cwd=REPO, text=True, capture_output=True).stdout


def critical_path_snapshot() -> dict:
    out = _run("python3", str(REPO / "lean4/scripts/critical_path.py"))
    try:
        return json.loads(out)
    except Exception:
        return {}


def closurestatus_groups() -> tuple[int, int, list[dict]]:
    """Return (ai_count, baseline_count, ai_chapters)."""
    sys.path.insert(0, str(REPO / "lean4/scripts"))
    from bedc_ci import collect_closurestatus_blocks, PAPER_PARTS_ROOT  # type: ignore
    blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    ai = [b for b in blocks if b.get("origin") == "ai"]
    base = [b for b in blocks if b.get("origin") != "ai"]
    return len(ai), len(base), ai


def round_throughput(log: Path, hours: int = 24) -> tuple[int, int, int]:
    """Return (success, failed, recovered) since N hours ago."""
    if not log.exists():
        return 0, 0, 0
    cutoff = datetime.now() - timedelta(hours=hours)
    cutoff_s = cutoff.strftime("%Y-%m-%d %H:%M:%S")
    success = failed = recovered = 0
    try:
        with log.open() as f:
            for line in f:
                if line[:19] < cutoff_s[:19]:
                    continue
                if "Round SUCCESS" in line:
                    success += 1
                if "Round FAILED" in line:
                    failed += 1
                if "RECOVERED" in line:
                    recovered += 1
    except OSError:
        pass
    return success, failed, recovered


def gate_fail_summary(log: Path, hours: int = 24) -> Counter:
    """Count gate-fail kinds in last N hours."""
    counter: Counter = Counter()
    if not log.exists():
        return counter
    cutoff = datetime.now() - timedelta(hours=hours)
    cutoff_s = cutoff.strftime("%Y-%m-%d %H:%M:%S")
    pat = re.compile(r"Pre-merge hard gate failed: (\S+)")
    try:
        with log.open() as f:
            for line in f:
                if line[:19] < cutoff_s[:19]:
                    continue
                m = pat.search(line)
                if m:
                    counter[m.group(1)] += 1
    except OSError:
        pass
    return counter


def stuck_in_recovery(log: Path, hours: int = 12) -> list[str]:
    """Return rounds queued > N hours ago without RECOVERED / unrecoverable terminator."""
    if not log.exists():
        return []
    cutoff = datetime.now() - timedelta(hours=hours)
    cutoff_s = cutoff.strftime("%Y-%m-%d %H:%M:%S")
    started: dict[str, str] = {}
    terminated: set[str] = set()
    try:
        with log.open() as f:
            for line in f:
                if line[:19] >= cutoff_s[:19]:
                    continue  # only old ones
                m = re.search(r"\[recovery\] queued (\S+)\.json for codex-(R\d+|P\d+)", line)
                if m:
                    started[m.group(2)] = line[:19]
                m = re.search(r"codex-(R\d+|P\d+)\s+(RECOVERED|unrecoverable)", line)
                if m:
                    terminated.add(m.group(1))
    except OSError:
        pass
    return [r for r in started if r not in terminated]


def recent_commits(hours: int = 24) -> list[str]:
    out = _run("git", "log", f"--since={hours} hours ago", "--oneline", "--no-merges")
    return [l for l in out.splitlines() if l.strip()]


def recent_prompt_edits(hours: int = 24) -> list[str]:
    out = _run(
        "git", "log", f"--since={hours} hours ago",
        "--oneline", "--", "papers/bedc/scripts/prompts/", "lean4/scripts/prompts/"
    )
    return [l for l in out.splitlines() if l.strip()]


def main() -> int:
    now = datetime.now()
    print(f"# BEDC daily report — {now.strftime('%Y-%m-%d %H:%M')}")
    print()
    print("## Pipeline state")
    cp = critical_path_snapshot()
    if cp:
        ch = cp.get("closed_horizons", {})
        closed = sum(ch.values())
        opn = cp.get("open_horizons", 0)
        print(f"- closed total: {closed}")
        print(f"- open: {opn}")
        for k in sorted(ch):
            print(f"  - {k}: {ch[k]}")
        print(f"- drift_chapters: {cp.get('drift_chapters_total', 0)}")
        print(f"- bridge_candidates: {cp.get('bridge_candidates_total', 0)}")
        print(f"- bridge_sync_pending: {cp.get('bridge_sync_pending_total', 0)}")
        print(f"- formal_axis_top: {cp.get('formal_axis_top_total', 0)}")
    print()
    print("## Chapter origin distribution")
    ai_n, base_n, ai_blocks = closurestatus_groups()
    print(f"- baseline (origin=human or unset): {base_n}")
    print(f"- ai-proposed (origin=ai): {ai_n}")
    if ai_blocks:
        for b in ai_blocks:
            print(f"  - {b['region']}Up at {b.get('theory_closure')} / {b.get('formal_status')}")
    print()
    print("## Throughput (last 24h)")
    p_s, p_f, p_r = round_throughput(PAPER_LOG)
    l_s, l_f, l_r = round_throughput(LEAN_LOG)
    print(f"- paper rounds: {p_s} success / {p_f} failed / {p_r} recovered")
    print(f"- lean rounds:  {l_s} success / {l_f} failed / {l_r} recovered")
    print()
    print("## Gate failures (last 24h)")
    p_gates = gate_fail_summary(PAPER_LOG)
    l_gates = gate_fail_summary(LEAN_LOG)
    if p_gates or l_gates:
        for k, v in (p_gates + l_gates).most_common():
            print(f"- {k}: {v}")
    else:
        print("- (none)")
    print()
    print("## Stuck in recovery > 12h")
    stuck = stuck_in_recovery(PAPER_LOG) + stuck_in_recovery(LEAN_LOG)
    if stuck:
        for r in stuck:
            print(f"- {r}")
    else:
        print("- (none)")
    print()
    print("## Recent commits (last 24h)")
    commits = recent_commits()
    print(f"- total: {len(commits)}")
    for c in commits[:10]:
        print(f"  - {c}")
    if len(commits) > 10:
        print(f"  - ... and {len(commits) - 10} more")
    print()
    print("## Prompt edits (last 24h)")
    pe = recent_prompt_edits()
    if pe:
        for c in pe:
            print(f"- {c}")
    else:
        print("- (none — pipeline self-evolving via existing prompts)")
    print()
    print("## Operator action items")
    items: list[str] = []
    if stuck:
        items.append(f"investigate {len(stuck)} round(s) stuck in recovery")
    if (p_gates + l_gates).most_common(1):
        kind, n = (p_gates + l_gates).most_common(1)[0]
        if n >= 5:
            items.append(f"recurring `{kind}` gate fail ({n} times) — consider prompt patch")
    if cp.get("formal_axis_top_total", 0) >= 50:
        items.append(f"formal_axis drift at {cp['formal_axis_top_total']} — paper-side may be lagging")
    if not items:
        print("- (none — pipeline healthy)")
    else:
        for it in items:
            print(f"- {it}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
