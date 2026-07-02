#!/usr/bin/env python3
"""Standalone BEDC -> mathlib bridge daemon.

Runs the bridge-round loop (candidate_filter -> isolated worktree -> codex
writes exactly one ExportWitness bridge row -> load-gated bridge_heavy_check ->
merge to codex-auto-dev) as its OWN process, so the mathlib-heavy Lake build
does not share the main lean orchestrator's process/thread and can be stopped
independently.

Single source of truth: the bridge machinery lives in ``codex_formalize.py``
(``run_bridge_round`` and helpers). This module only adds the standalone process
wrapper: a PID lock (single-flight), load- and memory-gates so the daemon never
starves the main pipeline, a hardened worker-prompt contract, and fail-closed
looping.

The bridge project is a separate ``require mathlib`` package under
``papers/bedc_mathlib_bridge``; nothing here touches the mathlib-free 0-axiom
BEDC core.

Usage:
  python3 lean4/scripts/codex_bridge.py                # resident daemon
  python3 lean4/scripts/codex_bridge.py --once         # one gated cycle, exit
  python3 lean4/scripts/codex_bridge.py --dry-run      # list candidates only
"""
from __future__ import annotations

import argparse
import fcntl
import os
import sys
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

# codex_formalize.py guards its orchestrator start-up under ``if __name__ ==
# "__main__"``; importing it only defines the bridge helpers + config we reuse.
import codex_formalize as cf  # noqa: E402

PID_LOCK_PATH = Path("/tmp/.bedc_bridge.pid")

# Interval between cycles. The candidate pool is small and conservative, so an
# hourly cadence is enough; the daemon spends most of its life asleep or gated.
INTERVAL_SECONDS = int(os.environ.get("BRIDGE_ROUND_INTERVAL", "3600"))

# Gates. Deliberately conservative so the bridge only works in genuinely quiet
# windows and never competes with the memory-bound main pipeline (2/3 ceiling).
MAX_LOAD1 = float(os.environ.get("BEDC_BRIDGE_ROUND_MAX_LOAD", "8"))
MIN_AVAIL_RAM_GB = float(os.environ.get("BEDC_BRIDGE_MIN_AVAIL_RAM_GB", "6.0"))
MAX_SWAP_GB = float(os.environ.get("BEDC_BRIDGE_MAX_SWAP_GB", "8.0"))

# Hardened worker-prompt contract (adversarial-design consensus: /sshx triplet +
# gpt-pro). Appended to codex_formalize's BRIDGE_ROUND_PROMPT_TEMPLATE for this
# process only. Contains no ``{`` / ``}`` so it survives the template .format().
HARDENED_PROMPT_SUFFIX = """
Additional HARD REQUIREMENTS (bridge non-triviality gate). A row that fails any
of these is bookkeeping, not a bridge; prefer producing NOTHING over a fake or
trivial bridge (leave the worktree unchanged):
1. mathlib_target MUST be a pre-existing Mathlib declaration. You must not
   define, wrap, alias, rename, or re-derive it inside the bridge project. If no
   suitable pre-existing Mathlib declaration exists for this candidate, leave the
   worktree unchanged.
2. The mathlib target must live in a Mathlib.* namespace, never in BEDC.*,
   BedcMathlibBridge.*, or any generated namespace (this is anti-circularity:
   the bridge interprets BEDC into pre-existing math, it must not become the
   semantic source).
3. Provide a canonical readback (or toMathlib and ofMathlib) and prove the
   round-trip (left_inv and right_inv), OR, when the target is not a plain type
   equivalence, an accepted structure-preserving correspondence: the relevant
   operation, recurrence, order, or classifier must be shown preserved.
4. Transport AT LEAST ONE non-trivial theorem across the bridge. It must NOT be
   rfl, Iff.rfl, True.intro, x = x, or a mere restatement of an inverse lemma; it
   must depend on at least one pre-existing Mathlib theorem or structure, not
   only on the bridge's own inverse lemmas.
5. bedc_consumed_decl must be a real existing BEDC declaration under lean4/BEDC,
   not a fresh definition invented in this round.
The load-gated heavy check enforces the no-hollow / statement-shape /
no-back-edge / boundary-axioms / export-matrix guards and will reject a
bookkeeping row.
"""


@contextmanager
def pid_lock() -> Iterator[None]:
    """Single-flight guard so at most one codex_bridge runs at a time."""
    fd = os.open(PID_LOCK_PATH, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("[bridge] another codex_bridge already holds the PID lock; exiting", flush=True)
            raise SystemExit(0)
        os.ftruncate(fd, 0)
        os.write(fd, f"{os.getpid()}\n".encode())
        yield
    finally:
        try:
            fcntl.flock(fd, fcntl.LOCK_UN)
        except OSError:
            pass
        os.close(fd)


def gates_ok() -> tuple[bool, str]:
    """Return (ok, reason). Closed when the box is busy so we never starve main."""
    try:
        load1 = os.getloadavg()[0]
    except (AttributeError, OSError):
        load1 = 0.0
    if load1 >= MAX_LOAD1:
        return False, f"load {load1:.1f} >= {MAX_LOAD1:.1f}"
    try:
        _level, swap_gb, avail_gb = cf.memory_pressure_snapshot()
    except Exception:  # pragma: no cover - defensive
        swap_gb, avail_gb = 0.0, 99.0
    if avail_gb < MIN_AVAIL_RAM_GB:
        return False, f"avail RAM {avail_gb:.1f}GB < {MIN_AVAIL_RAM_GB:.1f}GB"
    if swap_gb > MAX_SWAP_GB:
        return False, f"swap {swap_gb:.1f}GB > {MAX_SWAP_GB:.1f}GB"
    return True, f"load={load1:.1f} avail={avail_gb:.1f}GB swap={swap_gb:.1f}GB"


def run_cycle(dry_run: bool) -> None:
    ok, why = gates_ok()
    if not ok:
        cf.logger.info(f"[bridge] gate closed ({why}); skip cycle")
        return
    if dry_run:
        candidates = cf._bridge_candidate_filter()
        decls = [c.get("bedc_decl") for c in candidates[:5]]
        cf.logger.info(f"[bridge] dry-run gate ok ({why}); {len(candidates)} eligible candidate(s): {decls}")
        return
    cf.logger.info(f"[bridge] gate ok ({why}); running one bridge round")
    produced = cf.run_bridge_round()
    cf.logger.info(f"[bridge] round produced={produced}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Standalone BEDC -> mathlib bridge daemon")
    parser.add_argument("--once", action="store_true", help="run a single gated cycle then exit")
    parser.add_argument("--dry-run", action="store_true", help="list eligible candidates without dispatching")
    parser.add_argument("--interval", type=int, default=INTERVAL_SECONDS, help="seconds between cycles")
    args = parser.parse_args()

    # Harden the shared prompt for this process only (does not mutate the file).
    cf.BRIDGE_ROUND_PROMPT_TEMPLATE = cf.BRIDGE_ROUND_PROMPT_TEMPLATE + HARDENED_PROMPT_SUFFIX

    with pid_lock():
        cf.logger.info(
            f"[bridge] codex_bridge started pid={os.getpid()} interval={args.interval}s "
            f"max_load={MAX_LOAD1} min_avail_ram={MIN_AVAIL_RAM_GB}GB max_swap={MAX_SWAP_GB}GB"
        )
        if args.once or args.dry_run:
            run_cycle(args.dry_run)
            return
        while True:
            try:
                run_cycle(False)
            except Exception as exc:  # fail-closed: log, never crash the daemon
                cf.logger.error(f"[bridge] cycle error: {exc}", exc_info=True)
            time.sleep(args.interval)


if __name__ == "__main__":
    main()
