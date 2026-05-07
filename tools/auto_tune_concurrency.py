#!/usr/bin/env python3
"""Auto-tune `.pipeline_parallel.json` based on critical_path state.

Reads `lean4/scripts/critical_path.py` JSON output. Sizes lean / paper
/ lean_lake to match the actual candidate supply so workers don't
starve (empty rounds → cooldown storms) and don't oversubscribe (OOM
+ lake build contention). Hot-reloaded by orchestrators on next round
dispatch.

Tuning:
  lean      = clamp(top_size + LEAN_BUFFER, LEAN_MIN, LEAN_MAX)
              (lean rounds need a sibling each; +buffer because paper
              rounds keep adding chapters into top)
  paper     = clamp(root_unblocks + PAPER_BUFFER, PAPER_MIN, PAPER_MAX)
              (root_unblock targets are paper's highest-leverage work;
              +buffer for closure_mark / theory_extension on rich chs)
  lean_lake = clamp(lean // LAKE_DIVISOR, LAKE_MIN, LAKE_MAX)
              (lake build is RAM-heavy, throttle separately from lean)

Run periodically (e.g. every 120s via a daemon, or one-shot from cron):
  python3 tools/auto_tune_concurrency.py            # write + report
  python3 tools/auto_tune_concurrency.py --dry-run  # report only
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CRITICAL_PATH = REPO_ROOT / "lean4/scripts/critical_path.py"
CONFIG = REPO_ROOT / ".pipeline_parallel.json"

# Tuning constants. Adjust here if the cluster's resource profile
# changes (e.g. moving from 16GB → 32GB RAM allows higher LEAN_MAX).
#
# LEAN_BUFFER reduced from 3 → 0 after observing chapter-dogpile
# lake-build failures: when top_size=7 and lean=11, 4+ extra workers
# necessarily picked overlapping chapters (NumFieldUp / FieldExtUp),
# producing duplicate-declaration build errors at merge. With
# lean = top_size, each worker has its own sibling front and the
# sibling claim mechanism inside critical_path keeps them
# non-overlapping. As top grows (paper unlocks new chapters),
# lean grows to match.
LEAN_BUFFER = 0
LEAN_MIN = 3
LEAN_MAX = 10

PAPER_BUFFER = 4
PAPER_MIN = 3
PAPER_MAX = 16

LAKE_DIVISOR = 5
LAKE_MIN = 1
LAKE_MAX = 3


def clamp(x: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, x))


def compute_target(cp_data: dict) -> dict:
    top = cp_data.get("top", [])
    top_size = len(top)
    sum_eff = sum(t.get("sibling_effective_unmarked", 0) for t in top)
    root_unblocks = cp_data.get("top_root_unblocks", [])
    root_unblock_count = len(root_unblocks)

    lean = clamp(top_size + LEAN_BUFFER, LEAN_MIN, LEAN_MAX)
    paper = clamp(root_unblock_count + PAPER_BUFFER, PAPER_MIN, PAPER_MAX)
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
        },
    }


def run_critical_path() -> dict:
    res = subprocess.run(
        ["python3", str(CRITICAL_PATH)],
        capture_output=True, text=True, check=True,
    )
    return json.loads(res.stdout)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--dry-run", action="store_true",
                    help="Print proposed values; do not write config.")
    args = p.parse_args()

    cp_data = run_critical_path()
    target = compute_target(cp_data)
    signals = target.pop("_signals")

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
