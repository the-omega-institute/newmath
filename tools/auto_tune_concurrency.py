#!/usr/bin/env python3
"""Auto-tune `.pipeline_parallel.json` + housekeeping.

Reads `lean4/scripts/critical_path.py` JSON output. Sizes lean / paper
/ lean_lake to match the actual candidate supply so workers don't
starve (empty rounds → cooldown storms) and don't oversubscribe (OOM
+ lake build contention). Hot-reloaded by orchestrators on next round
dispatch.

Demand-driven tuning:
  lean      = clamp(top_size + LEAN_BUFFER, LEAN_MIN, LEAN_MAX)
  paper     = clamp(root_unblocks + PAPER_BUFFER, PAPER_MIN, PAPER_MAX)
  lean_lake = clamp(lean // LAKE_DIVISOR, LAKE_MIN, LAKE_MAX)

Pressure-driven adjustments (applied AFTER demand-driven tuning):
  - load avg 5min > LOAD_HIGH        → lean -= 2, paper -= 2 (clamped to MIN)
  - mem avail (vm_stat) < RAM_LOW_GB → lean -= 4, lean_lake -= 1
  - disk used % > DISK_PRESSURE_PCT  → aggressive log retention (1 day)
  - disk used % > DISK_PANIC_PCT     → emergency log retention (6 hours)

Housekeeping (runs every tick, cheap):
  - log retention: delete logs older than LOG_RETENTION_DAYS in
    {papers/bedc/scripts/logs/, lean4/scripts/logs/, scripts/logs/}
  - stale worktree cleanup: any `.worktrees/round_R<N>` or
    `paper_P<N>` whose round id has had no orchestrator log activity
    in WORKTREE_STALE_MINUTES gets force-removed plus its branch.

Run periodically (e.g. every 300s via the autotune daemon):
  python3 tools/auto_tune_concurrency.py            # write + report + clean
  python3 tools/auto_tune_concurrency.py --dry-run  # report only
  python3 tools/auto_tune_concurrency.py --no-clean # skip housekeeping
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timedelta
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CRITICAL_PATH = REPO_ROOT / "lean4/scripts/critical_path.py"
CONFIG = REPO_ROOT / ".pipeline_parallel.json"

# System pressure thresholds (8-core MBP, 16 GB RAM, 460 GB disk).
LOAD_HIGH = 30.0            # 5-min load avg above this triggers concurrency cut
RAM_LOW_GB = 1.5            # vm_stat free + inactive below this triggers cut
DISK_PRESSURE_PCT = 85      # tighten log retention to 1 day
DISK_PANIC_PCT = 92         # tighten log retention to 6 hours

# Housekeeping retention.
LOG_RETENTION_DAYS_DEFAULT = 2
LOG_RETENTION_DAYS_PRESSURE = 1
LOG_RETENTION_DAYS_PANIC = 0.25  # ~6 hours

# Worktree stale heuristic: no orchestrator-log mention in N minutes.
# CRITICAL: must be larger than the max Phase C codex exec duration
# (phase_c_timeout=6000s = 100min). During Phase C the orchestrator log
# is silent for the round id since the codex subprocess writes its own
# log_tag file, not the main orchestrator.log. Cleaning a worktree mid-
# Phase-C produces a worker exception when Phase D tries to `cd wt.path`.
# 150min = 100min Phase C + 50min slack for Phase B + Phase D + merge.
WORKTREE_STALE_MINUTES = 150
LEAN_LOG = REPO_ROOT / "lean4" / "scripts" / "logs" / "orchestrator.log"
PAPER_LOG = REPO_ROOT / "papers" / "bedc" / "scripts" / "logs" / "orchestrator.log"
WORKTREES_DIR = REPO_ROOT / ".worktrees"

# Log directories pruned each tick (older than retention).
LOG_DIRS = [
    REPO_ROOT / "papers" / "bedc" / "scripts" / "logs",
    REPO_ROOT / "lean4" / "scripts" / "logs",
    REPO_ROOT / "scripts" / "logs",
]

# Tuning constants.
#
# ============================================================
# DO NOT CHANGE LEAN_MAX / PAPER_MAX — pinned at 20 by user
# directive (2026-05-11). The cap stays at 20 regardless of
# what the demand signals report. MIN / BUFFER may still be
# tuned for ramp-up behaviour, but ceiling = 20 is fixed.
#
# Sustainability rationale: with paper PDF moved out of round
# (paper_builder_daemon handles full build async) and lean
# R-rounds skipping in-round lake build (bg_builder handles
# it), per-round CPU cost is dominated by codex exec
# (network-bound), so 20+20 concurrent rounds is sustainable
# on an 8-core MBP with load avg ~10-12.
# ============================================================
LEAN_BUFFER = 0
LEAN_MIN = 6   # lowered 2026-05-12: allow scaling down when R-side demand
               # genuinely runs low (critical_path top + fallback both
               # small). Previously pinned at 12 as sustainability floor,
               # but that wasted worker slots on Phase-B-0-chars failures
               # during saturation. 6 keeps a warm pool ready to absorb
               # new top entries as paper rounds advance closure_mark.
LEAN_MAX = 20  # DO NOT CHANGE — pinned

PAPER_BUFFER = 4
PAPER_MIN = 12
PAPER_MAX = 20  # DO NOT CHANGE — pinned

LAKE_DIVISOR = 5
LAKE_MIN = 2
LAKE_MAX = 3


def clamp(x: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, x))


def compute_target(cp_data: dict) -> dict:
    top = cp_data.get("top", [])
    top_size = len(top)
    sum_eff = sum(t.get("sibling_effective_unmarked", 0) for t in top)
    root_unblocks = cp_data.get("top_root_unblocks", [])
    root_unblock_count = len(root_unblocks)
    # Fallback signals when `top` is empty (frontier saturated): the
    # pipeline still has work to do — drift sync, bridge sync, formal-
    # axis catch-up, rotation transitions. Floor the worker count by
    # these so the cluster keeps producing rounds.
    drift = cp_data.get("drift_chapters_total", 0)
    bridge = cp_data.get("bridge_candidates_total", 0)
    bridge_sync = cp_data.get("bridge_sync_pending_total", 0)
    formal_top = cp_data.get("formal_axis_top_total", 0)
    fallback_demand = drift + bridge + bridge_sync + formal_top

    lean_demand = max(top_size, fallback_demand // 5)
    paper_demand = max(root_unblock_count, fallback_demand // 3)

    lean = clamp(lean_demand + LEAN_BUFFER, LEAN_MIN, LEAN_MAX)
    paper = clamp(paper_demand + PAPER_BUFFER, PAPER_MIN, PAPER_MAX)
    lean_lake = clamp(lean // LAKE_DIVISOR, LAKE_MIN, LAKE_MAX)

    return {
        "lean": lean,
        "paper": paper,
        "lean_lake": lean_lake,
        "_signals": {
            "top_size": top_size,
            "sum_effective_unmarked": sum_eff,
            "root_unblock_count": root_unblock_count,
            "open_horizons": cp_data.get("open_horizons", 0),
            "drift_chapters_total": drift,
            "bridge_candidates_total": bridge,
            "bridge_sync_pending_total": bridge_sync,
            "formal_axis_top_total": formal_top,
        },
    }


def run_critical_path() -> dict:
    res = subprocess.run(
        ["python3", str(CRITICAL_PATH)],
        capture_output=True, text=True, check=True,
    )
    return json.loads(res.stdout)


def read_system_metrics() -> dict:
    """Best-effort read of CPU load / RAM avail / disk usage on macOS."""
    metrics: dict[str, float] = {}
    try:
        load1, load5, load15 = os.getloadavg()
        metrics["load_1min"] = load1
        metrics["load_5min"] = load5
        metrics["load_15min"] = load15
    except OSError:
        pass
    # vm_stat: free + inactive pages, page size 4096
    try:
        r = subprocess.run(["vm_stat"], capture_output=True, text=True, timeout=5)
        free = inactive = 0
        for line in r.stdout.splitlines():
            if line.startswith("Pages free:"):
                free = int(line.rsplit(":", 1)[1].strip().rstrip("."))
            elif line.startswith("Pages inactive:"):
                inactive = int(line.rsplit(":", 1)[1].strip().rstrip("."))
        metrics["mem_avail_gb"] = (free + inactive) * 4096 / (1024 ** 3)
    except Exception:
        pass
    try:
        usage = shutil.disk_usage(str(REPO_ROOT))
        metrics["disk_used_pct"] = 100.0 * (usage.total - usage.free) / usage.total
        metrics["disk_avail_gb"] = usage.free / (1024 ** 3)
    except Exception:
        pass
    return metrics


def apply_pressure_adjustments(target: dict, metrics: dict) -> dict:
    """Mutate target dict downward when load/RAM is high. Returns notes."""
    notes: list[str] = []
    load5 = metrics.get("load_5min", 0.0)
    mem_avail = metrics.get("mem_avail_gb", 99.0)
    if load5 > LOAD_HIGH:
        before = (target["lean"], target["paper"])
        target["lean"] = clamp(target["lean"] - 2, LEAN_MIN, LEAN_MAX)
        target["paper"] = clamp(target["paper"] - 2, PAPER_MIN, PAPER_MAX)
        notes.append(f"load5={load5:.1f}>{LOAD_HIGH:.0f}: lean {before[0]}→{target['lean']}, paper {before[1]}→{target['paper']}")
    if mem_avail < RAM_LOW_GB:
        before = (target["lean"], target["lean_lake"])
        target["lean"] = clamp(target["lean"] - 4, LEAN_MIN, LEAN_MAX)
        target["lean_lake"] = clamp(target["lean_lake"] - 1, LAKE_MIN, LAKE_MAX)
        notes.append(f"mem_avail={mem_avail:.1f}GB<{RAM_LOW_GB}: lean {before[0]}→{target['lean']}, lean_lake {before[1]}→{target['lean_lake']}")
    return {"adjustments": notes}


def cleanup_old_logs(retention_days: float, dry_run: bool = False) -> dict:
    """Delete files in LOG_DIRS older than retention_days. Returns stats."""
    cutoff = time.time() - retention_days * 86400
    removed = 0
    bytes_freed = 0
    for ld in LOG_DIRS:
        if not ld.exists():
            continue
        for p in ld.rglob("*"):
            try:
                if not p.is_file():
                    continue
                st = p.stat()
                if st.st_mtime < cutoff:
                    bytes_freed += st.st_size
                    removed += 1
                    if not dry_run:
                        p.unlink()
            except FileNotFoundError:
                pass
            except Exception:
                pass
    return {
        "logs_removed": removed,
        "logs_mb_freed": round(bytes_freed / 1024 / 1024, 1),
        "retention_days": retention_days,
    }


_ROUND_DIR_RE = re.compile(r"^(round_R|paper_P)([0-9]+)$")


def cleanup_stale_worktrees(stale_minutes: int = WORKTREE_STALE_MINUTES,
                            dry_run: bool = False) -> dict:
    """Force-remove worktrees with no orchestrator-log activity in N minutes.

    Heuristic: scan `.worktrees/round_R*` and `paper_P*`, grep each id in the
    corresponding orchestrator log, find last mention. If older than
    stale_minutes, the worktree is abandoned. Skip if recovery_queue has a
    ticket for it.
    """
    if not WORKTREES_DIR.exists():
        return {"stale_removed": 0}
    recovery_queue = REPO_ROOT / ".recovery_queue"
    queued_ids: set[str] = set()
    if recovery_queue.exists():
        for f in recovery_queue.iterdir():
            m = re.match(r"^(R[0-9]+|P[0-9]+)_", f.name)
            if m:
                queued_ids.add(m.group(1))

    # Pre-read both orchestrator logs once (last 4 MB each is enough; 30-45min span)
    def read_tail(p: Path, mb: int = 4) -> str:
        if not p.exists():
            return ""
        try:
            size = p.stat().st_size
            with p.open("rb") as f:
                if size > mb * 1024 * 1024:
                    f.seek(size - mb * 1024 * 1024)
                return f.read().decode("utf-8", errors="ignore")
        except Exception:
            return ""

    lean_log = read_tail(LEAN_LOG, mb=6)
    paper_log = read_tail(PAPER_LOG, mb=6)

    now = datetime.now()
    cutoff_ts = (now - timedelta(minutes=stale_minutes)).strftime("%Y-%m-%d %H:%M:%S")

    # Build map of worktree paths held by live codex exec processes.
    # During Phase C the orchestrator log is silent for the round id
    # (codex writes its own log_tag file), so we MUST not classify it
    # stale just because the main log has no recent mention. The codex
    # subprocess is invoked with `-C <wt-path>`, so the path appears in
    # ps's command line. Any worktree referenced by an active process is
    # considered NOT stale regardless of log timestamp.
    held_paths: set[str] = set()
    try:
        ps_out = subprocess.run(
            ["ps", "-axo", "command"],
            capture_output=True, text=True, timeout=10,
        ).stdout
        for line in ps_out.splitlines():
            # Match `-C /path/to/.worktrees/<name>` segment.
            m_ps = re.search(r"-C\s+(/\S*\.worktrees/[^\s]+)", line)
            if m_ps:
                held_paths.add(m_ps.group(1).rstrip("/"))
    except Exception:
        pass

    stale: list[tuple[str, str, str]] = []  # (round_id, branch_name, wt_path)
    for wt in WORKTREES_DIR.iterdir():
        if not wt.is_dir():
            continue
        m = _ROUND_DIR_RE.match(wt.name)
        if not m:
            continue
        prefix, num = m.groups()
        if prefix == "round_R":
            rid = f"R{num}"
            branch = f"codex-R{num}"
            log_text = lean_log
        else:
            rid = f"P{num}"
            branch = f"paper-P{num}"
            log_text = paper_log
        if rid in queued_ids:
            continue
        if str(wt) in held_paths:
            # An active codex subprocess holds this worktree; do NOT touch.
            continue
        # Find last mention of [Rnnn] or [Pnnn]
        last_ts = ""
        for line in log_text.splitlines():
            if f"[{rid}]" in line:
                last_ts = line[:19]  # YYYY-MM-DD HH:MM:SS
        if not last_ts:
            # Worktree exists but never mentioned in tail; old enough to clear
            stale.append((rid, branch, str(wt)))
            continue
        if last_ts < cutoff_ts:
            stale.append((rid, branch, str(wt)))

    removed = 0
    for rid, branch, wt_path in stale:
        if dry_run:
            removed += 1
            continue
        try:
            subprocess.run(
                ["git", "worktree", "remove", "--force", wt_path],
                cwd=REPO_ROOT, capture_output=True, timeout=30,
            )
            subprocess.run(
                ["git", "branch", "-D", branch],
                cwd=REPO_ROOT, capture_output=True, timeout=10,
            )
            removed += 1
        except Exception:
            pass
    return {"stale_removed": removed, "stale_inspected": len(stale)}


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--dry-run", action="store_true",
                    help="Print proposed values; do not write config or delete files.")
    p.add_argument("--no-clean", action="store_true",
                    help="Skip log retention and stale-worktree cleanup.")
    args = p.parse_args()

    metrics = read_system_metrics()
    print(
        f"metrics: load5={metrics.get('load_5min', '?'):.2f if isinstance(metrics.get('load_5min'), float) else 's'} "
        f"mem_avail={metrics.get('mem_avail_gb', 0):.1f}GB "
        f"disk_used={metrics.get('disk_used_pct', 0):.1f}% "
        f"disk_avail={metrics.get('disk_avail_gb', 0):.1f}GB",
        file=sys.stderr,
    ) if False else None  # keep formatting simple; print plain below
    metric_summary = (
        f"metrics: load5={metrics.get('load_5min', 0):.2f} "
        f"mem_avail={metrics.get('mem_avail_gb', 0):.1f}GB "
        f"disk_used={metrics.get('disk_used_pct', 0):.1f}% "
        f"disk_avail={metrics.get('disk_avail_gb', 0):.1f}GB"
    )
    print(metric_summary, file=sys.stderr)

    cp_data = run_critical_path()
    target = compute_target(cp_data)
    signals = target.pop("_signals")
    pressure_notes = apply_pressure_adjustments(target, metrics)
    if pressure_notes["adjustments"]:
        for note in pressure_notes["adjustments"]:
            print(f"pressure: {note}", file=sys.stderr)

    # Housekeeping: log retention + stale worktree cleanup.
    if not args.no_clean:
        disk_pct = metrics.get("disk_used_pct", 0.0)
        if disk_pct >= DISK_PANIC_PCT:
            retention = LOG_RETENTION_DAYS_PANIC
            print(f"housekeeping: PANIC disk_used={disk_pct:.1f}%, retention {retention}d", file=sys.stderr)
        elif disk_pct >= DISK_PRESSURE_PCT:
            retention = LOG_RETENTION_DAYS_PRESSURE
            print(f"housekeeping: pressure disk_used={disk_pct:.1f}%, retention {retention}d", file=sys.stderr)
        else:
            retention = LOG_RETENTION_DAYS_DEFAULT
        log_stats = cleanup_old_logs(retention_days=retention, dry_run=args.dry_run)
        if log_stats["logs_removed"]:
            print(
                f"cleanup_logs: removed={log_stats['logs_removed']} "
                f"mb_freed={log_stats['logs_mb_freed']} retention={retention}d",
                file=sys.stderr,
            )
        wt_stats = cleanup_stale_worktrees(dry_run=args.dry_run)
        if wt_stats.get("stale_removed", 0):
            print(
                f"cleanup_worktrees: stale_removed={wt_stats['stale_removed']} "
                f"inspected={wt_stats.get('stale_inspected', 0)}",
                file=sys.stderr,
            )

    # Tolerate missing config file: sync daemon's stash/restore cycles
    # have been observed deleting it. The orchestrator falls back to
    # built-in defaults when the file is missing, so a missing CONFIG
    # is recoverable: we just write a fresh one with the autotune
    # values + empty seed for the rest.
    try:
        config = json.loads(CONFIG.read_text())
    except FileNotFoundError:
        config = {
            "phase_b_timeout": 3600,
            "phase_c_timeout": 6000,
            "paper_review_timeout": 1800,
            "paper_revise_timeout": 3600,
        }
    keys = ("paper", "lean", "lean_lake")

    diffs = []
    for k in keys:
        cur = config.get(k)
        new = target[k]
        if cur != new:
            diffs.append(f"{k}: {cur} → {new}")
            config[k] = new

    print(
        f"signals: top_size={signals['top_size']}, "
        f"sum_eff_unmarked={signals['sum_effective_unmarked']}, "
        f"root_unblocks={signals['root_unblock_count']}, "
        f"open_horizons={signals['open_horizons']}",
        file=sys.stderr,
    )

    if not diffs:
        print("no concurrency change needed", file=sys.stderr)
        return 0

    print(f"proposed: {', '.join(diffs)}", file=sys.stderr)
    if args.dry_run:
        return 0

    # Preserve trailing newline + 2-space indent for diff readability.
    CONFIG.write_text(json.dumps(config, indent=2) + "\n")
    print(f"wrote {CONFIG.relative_to(REPO_ROOT)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
