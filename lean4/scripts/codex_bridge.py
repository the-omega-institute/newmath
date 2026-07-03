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
import json
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

# Candidate rotation: candidate_filter re-nominates the same top-scored carrier
# every cycle, but some candidates cannot be bridged 0-axiom (e.g. Option needs
# Quot.sound/propext) and fail the heavy check every time. Without rotation the
# daemon would hammer the same failing candidate forever. Record a failed
# candidate and skip it for a cooldown so the daemon rotates through the pool.
FAILED_STATE_PATH = Path("/tmp/.bedc_bridge_failed.json")
FAIL_COOLDOWN_SECONDS = int(os.environ.get("BEDC_BRIDGE_FAIL_COOLDOWN", str(6 * 3600)))

# Discovery feeder. candidate_filter's autonomous-bridge universe (hardcoded
# ANCHOR_PATTERNS) has its 0-axiom-able members already bridged, and the
# remaining eligible carriers need classical axioms, so the bridge round almost
# always fail-closes. But there IS a large un-bridged tail of combinatorial /
# number-theoretic carriers that the operator's feat-bridge PR flow bridges by
# hand. Each cycle we emit that tail (un-contested by any open feat-bridge
# branch, not yet in MATRIX) as a worklist so the daemon is useful as a
# discovery feeder even when its own bridge round produces nothing. Read-only;
# never bridges and never guesses a mathlib target (that stays with the author).
REPO_ROOT = SCRIPT_DIR.parent.parent
COVERAGE_GAP_SCRIPT = REPO_ROOT / "papers" / "bedc_mathlib_bridge" / "scripts" / "bridge_coverage_gap.py"
WORKLIST_PATH = Path("/tmp/.bedc_bridge_worklist.json")


def emit_coverage_gap() -> None:
    import subprocess
    try:
        out = subprocess.run(
            [sys.executable, str(COVERAGE_GAP_SCRIPT), "--json"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=120,
        )
        if out.returncode != 0 or not out.stdout.strip():
            cf.logger.info(f"[bridge] coverage-gap emit skipped (rc={out.returncode})")
            return
        data = json.loads(out.stdout)
        WORKLIST_PATH.write_text(out.stdout)
        top = [r["carrier"] for r in data.get("worklist", [])[:8]]
        cf.logger.info(
            f"[bridge] coverage-gap: {data.get('uncontested_unbridged')} "
            f"uncontested-unbridged (of {data.get('total_bridge_shaped_carriers')} "
            f"bridge-shaped, {data.get('contested_open_feat_bridge')} contested); "
            f"top={top} -> {WORKLIST_PATH}"
        )
    except Exception as e:  # a feeder failure must never break the bridge cycle
        cf.logger.info(f"[bridge] coverage-gap emit error: {e}")


def _candidate_decl(candidate: dict) -> str:
    return str(candidate.get("bedc_decl") or candidate.get("bedc_irreducible_decl") or "")


def _load_failed() -> dict:
    try:
        data = json.loads(FAILED_STATE_PATH.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def _record_failed(decl: str) -> None:
    if not decl:
        return
    now = time.time()
    failed = _load_failed()
    failed[decl] = now
    # Prune entries older than the cooldown so the file stays small.
    failed = {k: v for k, v in failed.items() if now - float(v) < FAIL_COOLDOWN_SECONDS}
    try:
        FAILED_STATE_PATH.write_text(json.dumps(failed), encoding="utf-8")
    except OSError:
        pass


def _reorder_candidates(candidates: list) -> list:
    """Non-cooling candidates first (stable), so run_bridge_round's [0] rotates."""
    now = time.time()
    failed = _load_failed()

    def cooling(candidate: dict) -> bool:
        ts = failed.get(_candidate_decl(candidate))
        return ts is not None and (now - float(ts)) < FAIL_COOLDOWN_SECONDS

    fresh = [c for c in candidates if not cooling(c)]
    cooling_list = [c for c in candidates if cooling(c)]
    return fresh + cooling_list

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
6. AXIOM DISCIPLINE. An exported_core row must be 0-axiom: it must NOT depend on
   Quot.sound, propext, or Classical.choice (the BridgeAxiomGuard rejects an
   exported_core row that leaks any of these with BEDC_GATE_A_AXIOM). Many
   mathlib targets (quotients, Option/decidable-equality objects, anything whose
   equivalence needs quotient soundness or propositional extensionality) cannot
   be bridged 0-axiom. For such a candidate, do ONE of:
     (a) write a measured_boundary row instead of exported_core — set kind to
         measured_boundary in the MATRIX metadata, record the exact axioms in
         the boundary axiom ledger, and follow an existing measured_boundary
         template. This is still a real, honest bridge (it records where BEDC's
         constructivity stops and what mathlib axioms the correspondence costs);
     (b) if you cannot produce a clean exported_core OR a clean measured_boundary
         row, leave the worktree UNCHANGED.
   Never force an exported_core row that will fail the axiom guard.
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


STRUCTURAL_BRIDGE_PROMPT_SUFFIX = """

Structural-carrier bridge (the ONLY bridge kind this daemon may produce).
The candidate is a genuine BEDC STRUCTURAL carrier: a `structure` / `inductive`
(or a carrier `Type` with BEDC-defined operations and relations), e.g. the
GaussInt / ZMod / EisInt / TaggedOptionHistoryCarrier / ListHistoryCarrier /
SumHistoryCarrier class. Your job is to connect the BEDC OBJECT to a mathlib
OBJECT, not a Nat value to a Nat function.

HARD anti-laundering rules (a violation must make you leave the worktree
unchanged rather than ship it):
- FORBIDDEN: a Nat-value facade. Do NOT write `f n = Nat.<fn> n` /
  `bwordLength (natToUnary (g (bwordLength ...))) = Nat.<fn>` or any equality
  whose BEDC side reduces to a plain `Nat -> ... -> Nat` recursion through a
  `natToUnary` / `bwordLength` identity round-trip. `bwordLength (natToUnary n)
  = n` is proven, so that round-trip carries no content (a dead anchor).
- REQUIRED: the bridge is a CARRIER / RELATION / ALGEBRAIC-STRUCTURE
  correspondence over the BEDC carrier. Concretely, write to/from maps between
  the BEDC carrier and the mathlib object and show they are mutually inverse (a
  carrier equivalence), and/or show the BEDC OPERATIONS/RELATIONS (defined in
  BEDC on that carrier, e.g. GaussAdd/GaussMul, zmodAdd/zmodMul, the tagged
  constructors) correspond to the mathlib operations. Use BEDC's OWN operations
  as the bridge source; never pull a mathlib operation back through to/from maps
  and pass it off as "the BEDC operation" (structure-grafting = laundering).
- The exported_core row's `correspondence_shape_guess` must be a structural
  shape (carrier_equiv / rel_equiv / ring_equiv / ...), and `mathlib_decl` must
  be a mathlib TYPE / STRUCTURE / relation (Option, List, Sum, GaussianInt,
  ZMod, QuadraticAlgebra, PythagoreanTriple, ...), never a `Nat.*` function.

If you cannot establish a genuine structural correspondence with a pre-existing
mathlib object under 0 axioms, LEAVE THE WORKTREE UNCHANGED (the daemon records
a fail-close and rotates). Producing nothing is correct; producing a Nat facade
is not. Never fabricate a correspondence that is not actually proven.
"""


def worklist_candidates() -> list:
    """Build bridge candidates from the coverage-gap worklist.

    This is what makes the daemon actually PRODUCE. Instead of feeding
    candidate_filter's exhausted anchor-pattern pool (whose 0-axiom-able members
    are already bridged and whose remainder — Option/Gcd/List/Sum — is classical
    and always fail-closes), hand the worker the un-contested, un-bridged
    combinatorial / number carriers (Bell/Catalan/CentralFactorial/...) that the
    operator's feat-bridge flow bridges successfully. Each candidate carries the
    carrier namespace + its concrete Nat-recursion decls; the worker finds the
    pre-existing mathlib counterpart (per the hardened prompt) and writes the
    exported_core bridge, or fail-closes on the ones needing classical axioms.
    The worklist already excludes MATRIX-classified and open-feat-bridge carriers
    (non-racing), so the daemon only claims the genuine long tail.
    """
    try:
        data = json.loads(WORKLIST_PATH.read_text())
    except Exception:
        return []
    # Fail-closed: the coverage-gap worklist is Nat-shadow-laundering-shaped and
    # marks itself daemon_eligible=False / NO_STRUCTURAL_CARRIER_CANDIDATE=True.
    # Never hand its rows to run_bridge_round, even if a future caller revives
    # this entry point (the adversarial challenge flagged the dormant path).
    if data.get("daemon_eligible") is False or data.get("NO_STRUCTURAL_CARRIER_CANDIDATE"):
        return []
    cands = []
    for row in data.get("worklist", []):
        decls = row.get("bridge_decls") or []
        if not decls:
            continue
        cands.append(
            {
                "bedc_decl": decls[0],
                "namespace": row.get("namespace"),
                "bridge_decls": decls,
                "carrier": row.get("carrier"),
                "mathlib_target_guess": None,
                "eligible": True,
                "source": "coverage-gap",
                "priority": row.get("priority", 0),
            }
        )
    cands.sort(key=lambda c: -int(c.get("priority", 0)))
    return cands


# Correspondence shapes that describe a genuine BEDC-object <-> mathlib-object
# bridge (a carrier / relation / algebraic-structure equivalence over a real
# BEDC carrier). Anything else -- pointwise_eq, bhist_readback, or an unknown
# shape -- is a Nat-value facade that admits the dead natToUnary/bwordLength
# round-trip, so it is NOT eligible for autonomous bridging.
_STRUCTURAL_SHAPES = frozenset(
    {
        "carrier_equiv",
        "rel_equiv",
        "relation_equiv",
        "ring_equiv",
        "group_equiv",
        "field_equiv",
        "module_equiv",
        "order_equiv",
        "predicate_equiv",
        "structure_equiv",
        "iso",
        "isomorphism",
    }
)


def _structural_only(source: list) -> list:
    """POSITIVE allowlist: accept ONLY genuine structural bridge candidates.

    candidate_filter surfaces a MIX: structural carriers (carrier_equiv over a
    real BEDC carrier -- TaggedOptionHistoryCarrier / ListHistoryCarrier /
    SumHistoryCarrier / GaussInt / ZMod class) AND Nat-value-facade candidates
    (pointwise_eq / bhist_readback to a `Nat.<fn>` target, e.g. NatGcd ->
    Nat.gcd, natChooseFn -> Nat.choose). The latter admit the dead `natToUnary
    (NatFn (bwordLength ...))` round-trip and export a Nat-vs-Nat identity, not a
    BEDC-object <-> mathlib bridge. The adversarial challenge showed a negative
    drop-list (drop only pointwise_eq -> Nat.*) leaks: candidate_filter's
    `bhist_readback` role and other non-pointwise shapes slip through. So this is
    a DEFAULT-DENY allowlist -- a candidate is accepted only when its
    correspondence shape is affirmatively structural AND its mathlib target is
    not a `Nat.*` facade. If that empties the pool the daemon idles honestly (an
    idle daemon beats a laundering one). This is the feeder guard; the trust
    boundary is the heavy-check anti-laundering gate."""
    kept = []
    for c in source or []:
        decl = c.get("bedc_decl")
        shape = str(c.get("correspondence_shape_guess") or "").strip()
        target = str(c.get("mathlib_target_guess") or c.get("mathlib_class_guess") or "")
        if shape not in _STRUCTURAL_SHAPES:
            cf.logger.info(
                f"[bridge] reject non-structural candidate {decl} "
                f"(shape={shape or 'none'} -> {target}); structural-only allowlist"
            )
            continue
        if target.startswith("Nat.") or target == "Nat":
            cf.logger.info(
                f"[bridge] reject Nat-facade candidate {decl} "
                f"(shape={shape} -> {target}); structural-only allowlist"
            )
            continue
        kept.append(c)
    return kept


def run_cycle(dry_run: bool) -> None:
    # emit_coverage_gap writes the coverage-gap worklist as READ-ONLY TELEMETRY.
    # It is deliberately NOT a daemon bridge source: its Nat-recursion
    # combinatorial carriers (binomial / Lah / Catalan / Stirling / polygonal /
    # ...) can only be bridged as Nat-shadow LAUNDERING -- the BEDC side is
    # `natToUnary (NatFn (bwordLength a) (bwordLength b))`, an identity
    # round-trip (`bwordLength (natToUnary n) = n` is proven) wrapping a plain
    # `Nat -> ... -> Nat` recursion, so the exported equality is a Nat-vs-Nat
    # identity, NOT a BEDC-object <-> mathlib bridge (violates bridge Rule 1;
    # the dead-anchor gate check_value_anchor.py fail-closes such rows). The
    # daemon bridges ONLY genuine structural carriers surfaced by
    # candidate_filter; when none are eligible it idles honestly rather than
    # manufacturing laundering.
    emit_coverage_gap()
    ok, why = gates_ok()
    if not ok:
        cf.logger.info(f"[bridge] gate closed ({why}); skip cycle")
        return
    source = _structural_only(cf._bridge_candidate_filter())
    candidates = _reorder_candidates(source)
    if not candidates:
        cf.logger.info(
            f"[bridge] gate ok ({why}); no eligible structural candidate "
            f"(Nat-shadow coverage-gap worklist is telemetry-only, not a bridge source)"
        )
        return
    picked = _candidate_decl(candidates[0])
    if dry_run:
        decls = [_candidate_decl(c) for c in candidates[:5]]
        cf.logger.info(f"[bridge] dry-run gate ok ({why}); {len(candidates)} candidate(s) picked={picked} order={decls}")
        return
    cf.logger.info(f"[bridge] gate ok ({why}); running bridge round on {picked}")
    # Pin run_bridge_round to our rotated order so it picks candidates[0].
    orig_filter = cf._bridge_candidate_filter
    cf._bridge_candidate_filter = lambda: candidates
    try:
        produced = cf.run_bridge_round()
    finally:
        cf._bridge_candidate_filter = orig_filter
    cf.logger.info(f"[bridge] round produced={produced} candidate={picked}")
    if not produced:
        _record_failed(picked)
        cf.logger.info(f"[bridge] {picked} entered fail-cooldown ({FAIL_COOLDOWN_SECONDS}s)")


def main() -> None:
    parser = argparse.ArgumentParser(description="Standalone BEDC -> mathlib bridge daemon")
    parser.add_argument("--once", action="store_true", help="run a single gated cycle then exit")
    parser.add_argument("--dry-run", action="store_true", help="list eligible candidates without dispatching")
    parser.add_argument("--interval", type=int, default=INTERVAL_SECONDS, help="seconds between cycles")
    args = parser.parse_args()

    # Harden the shared prompt for this process only (does not mutate the file).
    cf.BRIDGE_ROUND_PROMPT_TEMPLATE = (
        cf.BRIDGE_ROUND_PROMPT_TEMPLATE + HARDENED_PROMPT_SUFFIX + STRUCTURAL_BRIDGE_PROMPT_SUFFIX
    )

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
