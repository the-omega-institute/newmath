#!/usr/bin/env python3
"""Auto-tune `.pipeline_parallel.json` + housekeeping.

Reads `lean4/scripts/critical_path.py` JSON output. Sizes lean / paper
/ lean_lake to match the actual candidate supply so workers don't
starve (empty rounds → cooldown storms) and don't oversubscribe (OOM
+ lake build contention). Hot-reloaded by orchestrators on next round
dispatch.

Demand-driven tuning follows critical-path supply, then host capacity
and load gates keep the worker pool below the point where CPU contention
reduces throughput.

Pressure-driven adjustments:
  - load avg 5min > 1.5 * physical cores → scale target downward
  - load avg 5min >= 0.8 * physical cores → do not raise current concurrency
  - mem avail (vm_stat) < RAM_LOW_GB      → lean -= 4, lean_lake -= 1
  - disk used % > DISK_PRESSURE_PCT  → aggressive log retention (1 day)
  - disk used % > DISK_PANIC_PCT     → emergency log retention (6 hours)

Housekeeping (runs every tick, cheap):
  - log retention: delete logs older than LOG_RETENTION_DAYS in
    {papers/bedc/scripts/logs/, lean4/scripts/logs/, scripts/logs/}
  - stale worktree cleanup: semantic worker worktrees first; ordinal-shaped
    worktrees are cleanup remnants.

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

from pipeline_worker_identity import legacy_worktree_kind, parse_new_worktree_name

REPO_ROOT = Path(__file__).resolve().parent.parent
CRITICAL_PATH = REPO_ROOT / "lean4/scripts/critical_path.py"
CONFIG = REPO_ROOT / ".pipeline_parallel.json"

# System pressure thresholds.
LOAD_HIGH_PER_CORE = 1.5    # 5-min load avg above this scales concurrency down
LOAD_LOW_PER_CORE = 0.8     # below this, supply-driven upward movement is allowed
TOTAL_ACTIVE_PER_CORE = 1.25
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

# Tuning constants. Host-specific caps are derived from these legacy
# ceilings and the detected physical core count.
LEAN_BUFFER = 0
LEAN_MIN = 3
LEAN_MAX = 16
PAPER_BUFFER = 4
PAPER_MIN = 3
PAPER_MAX = 14
LAKE_DIVISOR = 5
LAKE_MIN = 1
LAKE_MAX = 3
MAX_TICK_DELTA = 2
MIN_CHANGE_DELTA = 2
CPU_COUNT_FALLBACK = 4


def clamp(x: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, x))


def read_physical_cores() -> int:
    """Return physical cores when available; fall back to logical CPUs."""
    try:
        res = subprocess.run(
            ["sysctl", "-n", "hw.physicalcpu"],
            capture_output=True, text=True, timeout=2,
        )
        if res.returncode == 0:
            cores = int(res.stdout.strip())
            if cores > 0:
                return cores
    except Exception:
        pass
    try:
        logical = os.cpu_count()
        if logical and logical > 0:
            return logical
    except Exception:
        pass
    return CPU_COUNT_FALLBACK


def host_caps(cores: int) -> dict[str, int]:
    paper_max = min(PAPER_MAX, max(PAPER_MIN, cores // 2))
    lean_max = min(LEAN_MAX, max(LEAN_MIN, cores))
    total_active_max = max(PAPER_MIN + LEAN_MIN, int(cores * TOTAL_ACTIVE_PER_CORE))
    lake_max = clamp(cores // 8, LAKE_MIN, 2)
    return {
        "paper_min": PAPER_MIN,
        "paper_max": paper_max,
        "lean_min": LEAN_MIN,
        "lean_max": lean_max,
        "total_active_max": total_active_max,
        "lake_min": LAKE_MIN,
        "lake_max": lake_max,
    }


def cap_total_active(paper: int, lean: int, caps: dict[str, int]) -> tuple[int, int]:
    total_max = caps["total_active_max"]
    if paper + lean <= total_max:
        return paper, lean

    paper_min = caps["paper_min"]
    lean_min = caps["lean_min"]
    extra_budget = max(0, total_max - paper_min - lean_min)
    paper_extra = max(0, paper - paper_min)
    lean_extra = max(0, lean - lean_min)
    extra_total = paper_extra + lean_extra
    if extra_total == 0:
        return paper_min, lean_min

    paper = paper_min + (extra_budget * paper_extra) // extra_total
    lean = lean_min + (extra_budget * lean_extra) // extra_total
    while paper + lean < total_max and (paper < caps["paper_max"] or lean < caps["lean_max"]):
        if lean_extra >= paper_extra and lean < caps["lean_max"]:
            lean += 1
        elif paper < caps["paper_max"]:
            paper += 1
        elif lean < caps["lean_max"]:
            lean += 1
        else:
            break
    while paper + lean > total_max:
        if lean > caps["lean_min"] and lean >= paper:
            lean -= 1
        elif paper > caps["paper_min"]:
            paper -= 1
        else:
            break
    return paper, lean


def load_adjusted_target(
    paper: int,
    lean: int,
    load5: float,
    cores: int,
    caps: dict[str, int],
) -> tuple[int, int, str | None]:
    high = LOAD_HIGH_PER_CORE * cores
    if load5 <= high:
        return paper, lean, None

    total_max = caps["total_active_max"]
    pressure_ratio = high / max(load5, 0.01)
    target_total = clamp(
        int(total_max * pressure_ratio),
        caps["paper_min"] + caps["lean_min"],
        total_max,
    )
    paper, lean = cap_total_active(paper, lean, {**caps, "total_active_max": target_total})
    return (
        paper,
        lean,
        f"load5={load5:.1f}>{high:.1f}: scaled active target to {paper + lean}/{total_max}",
    )


def apply_hysteresis(
    target: dict,
    current: dict | None,
    load5: float | None,
    cores: int,
    caps: dict[str, int],
) -> list[str]:
    if not current:
        return []

    notes: list[str] = []
    high = LOAD_HIGH_PER_CORE * cores
    low = LOAD_LOW_PER_CORE * cores
    overloaded = load5 is not None and load5 > high
    allow_raise = load5 is not None and load5 < low

    for key in ("paper", "lean", "lean_lake"):
        cur = current.get(key)
        if not isinstance(cur, int):
            continue
        wanted = target[key]
        if overloaded and wanted > cur:
            wanted = cur
        elif not allow_raise and wanted > cur:
            wanted = cur

        diff = wanted - cur
        if diff == 0:
            target[key] = cur
            continue
        if overloaded and diff < 0:
            target[key] = wanted
            notes.append(f"hysteresis: {key} {cur}→{target[key]}")
            continue
        if abs(diff) < MIN_CHANGE_DELTA:
            target[key] = cur
            notes.append(f"hysteresis: keep {key}={cur} (delta {diff:+d})")
            continue
        if diff > 0:
            diff = min(diff, MAX_TICK_DELTA)
        elif not overloaded:
            diff = max(diff, -MAX_TICK_DELTA)
        target[key] = cur + diff
        notes.append(f"hysteresis: {key} {cur}→{target[key]}")

    target["paper"] = clamp(target["paper"], caps["paper_min"], caps["paper_max"])
    target["lean"] = clamp(target["lean"], caps["lean_min"], caps["lean_max"])
    before_total_cap = (target["paper"], target["lean"])
    target["paper"], target["lean"] = cap_total_active(target["paper"], target["lean"], caps)
    after_total_cap = (target["paper"], target["lean"])
    if after_total_cap != before_total_cap:
        notes.append(
            "capacity: active "
            f"{before_total_cap[0]}+{before_total_cap[1]}→"
            f"{after_total_cap[0]}+{after_total_cap[1]} "
            f"(max {caps['total_active_max']})"
        )
    target["lean_lake"] = clamp(target["lean_lake"], caps["lake_min"], caps["lake_max"])
    return notes


def compute_target(
    cp_data: dict,
    metrics: dict | None = None,
    current: dict | None = None,
    cores: int | None = None,
) -> dict:
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

    metrics = metrics or {}
    cores = cores or read_physical_cores()
    caps = host_caps(cores)
    notes: list[str] = []

    lean = clamp(lean_demand + LEAN_BUFFER, caps["lean_min"], caps["lean_max"])
    paper = clamp(paper_demand + PAPER_BUFFER, caps["paper_min"], caps["paper_max"])
    paper, lean = cap_total_active(paper, lean, caps)

    load5 = metrics.get("load_5min")
    if isinstance(load5, (int, float)):
        paper, lean, note = load_adjusted_target(paper, lean, float(load5), cores, caps)
        if note:
            notes.append(note)

    lean_lake = clamp(lean // LAKE_DIVISOR, caps["lake_min"], caps["lake_max"])

    target = {
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
            "physical_cores": cores,
            "load_5min": load5 if isinstance(load5, (int, float)) else None,
            "load_low": LOAD_LOW_PER_CORE * cores,
            "load_high": LOAD_HIGH_PER_CORE * cores,
            "paper_max": caps["paper_max"],
            "lean_max": caps["lean_max"],
            "lean_lake_max": caps["lake_max"],
            "total_active_max": caps["total_active_max"],
            "lean_demand": lean_demand,
            "paper_demand": paper_demand,
            "notes": notes,
        },
    }
    notes.extend(apply_hysteresis(target, current, load5, cores, caps))
    return target


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
    except Exception:
        pass
    # vm_stat: free + inactive pages. Page size is 16384 on arm64 Macs
    # (Apple Silicon) and 4096 on Intel. Parse the first line of vm_stat
    # which reports `Mach Virtual Memory Statistics: (page size of N bytes)`.
    # Previously hard-coded 4096 under-reported memory by 4× on arm64,
    # falsely triggering RAM_LOW_GB pressure cut (real 2.5GB inactive read
    # as 0.6GB → lean 8→4 cap, halving R-side throughput silently for days).
    try:
        r = subprocess.run(["vm_stat"], capture_output=True, text=True, timeout=5)
        free = inactive = 0
        page_size = 4096
        import re as _vm_re
        for line in r.stdout.splitlines():
            m = _vm_re.search(r"page size of (\d+) bytes", line)
            if m:
                page_size = int(m.group(1))
                continue
            if line.startswith("Pages free:"):
                free = int(line.rsplit(":", 1)[1].strip().rstrip("."))
            elif line.startswith("Pages inactive:"):
                inactive = int(line.rsplit(":", 1)[1].strip().rstrip("."))
        metrics["mem_avail_gb"] = (free + inactive) * page_size / (1024 ** 3)
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
    """Mutate target dict downward when RAM is low. Returns notes."""
    notes: list[str] = []
    mem_avail = metrics.get("mem_avail_gb", 99.0)
    signals = target.get("_signals", {})
    caps = {
        "paper_min": PAPER_MIN,
        "paper_max": signals.get("paper_max", PAPER_MAX),
        "lean_min": LEAN_MIN,
        "lean_max": signals.get("lean_max", LEAN_MAX),
        "total_active_max": signals.get("total_active_max", LEAN_MIN + PAPER_MIN),
        "lake_min": LAKE_MIN,
        "lake_max": signals.get("lean_lake_max", LAKE_MAX),
    }
    if mem_avail < RAM_LOW_GB:
        before = (target["lean"], target["lean_lake"])
        target["lean"] = clamp(target["lean"] - 4, caps["lean_min"], caps["lean_max"])
        target["lean_lake"] = clamp(target["lean_lake"] - 1, caps["lake_min"], caps["lake_max"])
        target["paper"], target["lean"] = cap_total_active(target["paper"], target["lean"], caps)
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


def cleanup_stale_worktrees(stale_minutes: int = WORKTREE_STALE_MINUTES,
                            dry_run: bool = False) -> dict:
    """Force-remove worktrees with no orchestrator-log activity in N minutes.

    Heuristic: scan semantic worker worktrees and ordinal-shaped cleanup
    remnants, grep each id in the corresponding orchestrator log, find last mention. If older than
    stale_minutes, the worktree is abandoned. Skip if recovery_queue has a
    ticket for it.
    """
    if not WORKTREES_DIR.exists():
        return {"stale_removed": 0}
    recovery_queue = REPO_ROOT / ".recovery_queue"
    queued_ids: set[str] = set()
    if recovery_queue.exists():
        for f in recovery_queue.iterdir():
            queued_ids.add(f.name.rsplit("_", 1)[0])

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
        parsed = parse_new_worktree_name(wt.name)
        legacy = legacy_worktree_kind(wt.name)
        if not parsed and not legacy:
            continue
        if parsed:
            kind, slug, lease_id = parsed
            rid = wt.name
            branch = f"{kind}-{slug}-{lease_id}"
            log_text = lean_log if kind == "formalize" else paper_log
        elif legacy and legacy[0] == "formalize":
            rid = f"R{legacy[1]}"
            branch = "codex-R" + str(legacy[1])
            log_text = lean_log
        else:
            assert legacy is not None
            rid = f"P{legacy[1]}"
            branch = "paper-P" + str(legacy[1])
            log_text = paper_log
        if rid in queued_ids or wt.name in queued_ids:
            continue
        if str(wt) in held_paths:
            # An active codex subprocess holds this worktree; do NOT touch.
            continue
        last_ts = ""
        for line in log_text.splitlines():
            if f"[{rid}]" in line or rid in line:
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
    load5 = metrics.get("load_5min")
    load5_text = f"{load5:.2f}" if isinstance(load5, (int, float)) else "unknown"
    metric_summary = (
        f"metrics: load5={load5_text} "
        f"mem_avail={metrics.get('mem_avail_gb', 0):.1f}GB "
        f"disk_used={metrics.get('disk_used_pct', 0):.1f}% "
        f"disk_avail={metrics.get('disk_avail_gb', 0):.1f}GB"
    )
    print(metric_summary, file=sys.stderr)

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

    cp_data = run_critical_path()
    current = {k: config.get(k) for k in ("paper", "lean", "lean_lake")}
    target = compute_target(cp_data, metrics=metrics, current=current)
    signals = target["_signals"]
    for note in signals.get("notes", []):
        print(f"pressure: {note}", file=sys.stderr)
    pressure_notes = apply_pressure_adjustments(target, metrics)
    if pressure_notes["adjustments"]:
        for note in pressure_notes["adjustments"]:
            print(f"pressure: {note}", file=sys.stderr)
    target.pop("_signals")

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
    print(
        f"caps: cores={signals['physical_cores']} "
        f"paper_max={signals['paper_max']} lean_max={signals['lean_max']} "
        f"lean_lake_max={signals['lean_lake_max']} "
        f"total_active_max={signals['total_active_max']} "
        f"load_low={signals['load_low']:.1f} load_high={signals['load_high']:.1f}",
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
