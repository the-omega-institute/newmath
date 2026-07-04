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

# Discovery feeder. candidate_filter supplies structural candidates; the Nat
# sequence feeder supplies existing BEDC.Derived value sequences with conservative
# mathlib target hints. The policy filter below decides which rows may reach a
# bridge worker.
REPO_ROOT = SCRIPT_DIR.parent.parent
NAT_SEQUENCE_SCRIPT = (
    REPO_ROOT
    / "papers"
    / "bedc_mathlib_bridge"
    / "scripts"
    / "bridge_nat_sequence_candidates.py"
)
WORKLIST_PATH = Path("/tmp/.bedc_bridge_worklist.json")


def emit_coverage_gap() -> None:
    import subprocess
    try:
        out = subprocess.run(
            [sys.executable, str(NAT_SEQUENCE_SCRIPT), "--json"],
            capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=120,
        )
        if out.returncode != 0 or not out.stdout.strip():
            cf.logger.info(f"[bridge] nat-sequence emit skipped (rc={out.returncode})")
            return
        data = json.loads(out.stdout)
        WORKLIST_PATH.write_text(out.stdout)
        top = [r["carrier"] for r in data.get("worklist", [])[:8]]
        cf.logger.info(
            f"[bridge] nat-sequence: {data.get('eligible_candidates')} eligible "
            f"(of {data.get('uncontested_unbridged')} uncontested-unbridged, "
            f"{data.get('total_bridge_shaped_carriers')} bridge-shaped, "
            f"{data.get('contested_open_feat_bridge')} contested); "
            f"top={top} -> {WORKLIST_PATH}"
        )
    except Exception as e:  # a feeder failure must never break the bridge cycle
        cf.logger.info(f"[bridge] nat-sequence emit error: {e}")


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
    # Within fresh, try nat_value_sequence candidates (a BEDC Nat sequence proven
    # equal to a pre-existing mathlib Nat decl) before structural_object candidates.
    # The autonomous single-shot+repair worker reliably lands nat_value bridges but
    # not structural-carrier equivalences (Sum/Option/List history carriers always
    # fail-close), so leading with structural ones starves production: the daemon
    # burns every cycle fail-closing on a structural carrier and never reaches the
    # bridgeable nat_value candidates. Structural candidates still get their turn
    # after the fresh nat_value ones are exhausted or cooling.
    fresh_nat = [c for c in fresh if c.get("bridge_kind") == "nat_value_sequence"]
    fresh_other = [c for c in fresh if c.get("bridge_kind") != "nat_value_sequence"]
    return fresh_nat + fresh_other + cooling_list

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
2. The mathlib target must be supplied by the pre-existing mathlib/Lean
   environment, for example Nat.choose, Nat.factorial, Bool, GaussianInt, ZMod,
   or a named mathlib theorem surface. It must never be BEDC.*,
   BedcMathlibBridge.*, or any generated namespace (anti-circularity: the bridge
   interprets BEDC into pre-existing math, it must not become the semantic
   source).
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


HONEST_BRIDGE_PROMPT_SUFFIX = """

Allowed bridge kinds. The candidate JSON includes bridge_kind; follow it exactly.

A. structural_object
- The BEDC side is a genuine carrier, relation, algebraic object, or predicate
  with existing BEDC-defined operations or relations.
- Connect the BEDC object to a pre-existing mathlib object or relation by
  to/from maps, round trips, relation equivalence, or operation preservation.
- Use BEDC's own existing operations and relations as the source. Never pull a
  mathlib operation back through maps and present it as a BEDC operation.

B. nat_value_sequence
- The BEDC side is an existing BEDC.Derived Nat-valued sequence, count, or
  readback declaration. This is a pointwise/readback equality, not a carrier
  equivalence.
- The target is a pre-existing mathlib Nat declaration or formula surface such
  as Nat.choose, Nat.factorial, Nat.fib, Nat.centralBinom, Nat.descFactorial,
  Nat.superFactorial, or numDerangements.
- A nat_value_sequence mathlib target must be a genuine Mathlib declaration
  imported from Mathlib, not a Lean core Nat declaration; core Nat facts such
  as Nat.pow, Nat.mul, Nat.add, and Nat.gcd are rejected by ThinLayerGuard.
- The bridge must consume at least one existing BEDC theorem, recurrence,
  closed-form theorem, boundary theorem, or existing bridge theorem that itself
  consumes BEDC content. Do not introduce the BEDC source function in the bridge
  project.
- The theorem and MATRIX row must honestly say pointwise/readback equality. Do
  not claim carrier_equiv, ring_equiv, geometry, classification, enumeration,
  or full API equivalence for a Nat sequence.

Hard reject lines for both kinds:
- Bare Nat shadow: no existing BEDC.Derived source, or a bridge-side alias of a
  mathlib Nat function proved equal to itself.
- Dead anchor: the only BEDC contact is natToUnary around a Nat function of
  bwordLength inputs, with no BEDC theorem proving the source semantics.
- Structure grafting: mathlib operations pulled back and relabeled as BEDC
  operations.
- Hollow witnesses: rfl-only, x equals x, True, or inverse-lemma bookkeeping
  without a real correspondence theorem.

Nat value/readback templates:
- papers/bedc_mathlib_bridge/lean4/BedcMathlibBridge/Constructive/CakeNumber.lean
- papers/bedc_mathlib_bridge/lean4/BedcMathlibBridge/Export/CakeNumber.lean
- papers/bedc_mathlib_bridge/lean4/BedcMathlibBridge/Constructive/Lobb.lean
- papers/bedc_mathlib_bridge/lean4/BedcMathlibBridge/Export/Lobb.lean
- papers/bedc_mathlib_bridge/lean4/BedcMathlibBridge/Constructive/Raney.lean
- papers/bedc_mathlib_bridge/lean4/BedcMathlibBridge/Export/Raney.lean

If neither an honest structural_object bridge nor an honest nat_value_sequence
bridge is possible under the 0-axiom exported_core discipline, leave the
worktree unchanged.
"""


def worklist_candidates() -> list:
    """Build bridge candidates from the coverage-gap worklist.

    The worklist already excludes MATRIX-classified and open-feat-bridge
    carriers. Unknown mathlib targets remain in telemetry with eligible=false;
    the policy filter will keep only rows with conservative target hints and
    BEDC theorem evidence.
    """
    try:
        data = json.loads(WORKLIST_PATH.read_text())
    except Exception:
        return []
    cands = []
    for row in data.get("worklist", []):
        if not isinstance(row, dict):
            continue
        item = dict(row)
        decls = item.get("bridge_decls") or []
        if "bedc_decl" not in item and decls:
            item["bedc_decl"] = decls[0]
        item.setdefault("source", "nat-sequence-worklist")
        item.setdefault("correspondence_shape_guess", "pointwise_eq")
        cands.append(item)
    cands.sort(key=lambda c: -int(c.get("priority", 0)))
    return cands


STRUCTURAL_SHAPES = frozenset(
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
NAT_VALUE_SHAPES = frozenset(
    {
        "pointwise_eq",
        "nat_sequence_eq",
        "readback_eq",
        "bhist_readback",
    }
)
# Core (mathlib-free) Nat operations. A nat_value bridge whose target is one of
# these is a mathlib-free arithmetic fact — the bridge project's ThinLayerGuard
# rejects it ("belongs to BEDC core, not a bridge"), so surfacing such a candidate
# only wastes a daemon cycle. We deliberately do NOT keep a positive allow-list of
# acceptable targets: that couples candidate discovery to a brittle hand-maintained
# list and blocks the AI worker from finding any genuine Mathlib target on its own.
# The worker discovers a pre-existing Mathlib target; the heavy-check ThinLayerGuard
# + 0-axiom guard are the authoritative final gate. This is only a cheap up-front
# reject of the KNOWN mathlib-free targets when a candidate already carries a guess.
CORE_NAT_TARGETS = frozenset(
    {
        "Nat.pow",
        "Nat.mul",
        "Nat.add",
        "Nat.sub",
        "Nat.div",
        "Nat.mod",
        "Nat.gcd",
        "Nat.succ",
        "Nat",
    }
)


def _candidate_target(candidate: dict) -> str:
    return str(candidate.get("mathlib_target_guess") or candidate.get("mathlib_class_guess") or "")


def _is_structural_candidate(candidate: dict) -> bool:
    shape = str(candidate.get("correspondence_shape_guess") or "").strip()
    target = _candidate_target(candidate)
    return shape in STRUCTURAL_SHAPES and target != "Nat" and not target.startswith("Nat.")


def _is_nat_value_candidate(candidate: dict) -> bool:
    shape = str(candidate.get("correspondence_shape_guess") or "").strip()
    target = _candidate_target(candidate)
    decls = [candidate.get("bedc_decl"), *(candidate.get("bridge_decls") or [])]
    if candidate.get("source") == "nat-sequence-worklist" and candidate.get("eligible") is not True:
        return False
    if shape not in NAT_VALUE_SHAPES:
        return False
    # Accept a missing/None target — the worker finds a genuine pre-existing Mathlib
    # target and ThinLayerGuard verifies it is not a mathlib-free core fact. Only
    # reject a target that is already known to be a core (mathlib-free) op.
    if target and (target in CORE_NAT_TARGETS or target == "Nat"):
        return False
    if not any(str(decl).startswith("BEDC.Derived.") for decl in decls if decl):
        return False
    if not (
        candidate.get("has_recurrence_or_closedform_theorem")
        or candidate.get("bedc_source_theorem_guess")
        or candidate.get("bedc_consumed_decl_guess")
    ):
        return False
    return True


def _policy_filter(source: list) -> list:
    kept = []
    for candidate in source or []:
        decl = candidate.get("bedc_decl")
        shape = str(candidate.get("correspondence_shape_guess") or "").strip()
        target = _candidate_target(candidate)
        if _is_structural_candidate(candidate):
            candidate["bridge_kind"] = "structural_object"
            kept.append(candidate)
            continue
        if _is_nat_value_candidate(candidate):
            candidate["bridge_kind"] = "nat_value_sequence"
            kept.append(candidate)
            continue
        cf.logger.info(
            f"[bridge] reject candidate {decl} "
            f"(shape={shape or 'none'} -> {target or 'none'}); policy filter"
        )
    return kept


def run_cycle(dry_run: bool) -> None:
    emit_coverage_gap()
    ok, why = gates_ok()
    if not ok:
        cf.logger.info(f"[bridge] gate closed ({why}); skip cycle")
        return
    source = []
    source.extend(cf._bridge_candidate_filter())
    source.extend(worklist_candidates())
    candidates = _reorder_candidates(_policy_filter(source))
    if not candidates:
        cf.logger.info(f"[bridge] gate ok ({why}); no eligible honest bridge candidate")
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
        if getattr(cf, "BRIDGE_LAST_DEFERRED", False):
            cf.logger.info(f"[bridge] {picked} deferred by load gate; no fail-cooldown")
            return
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
        cf.BRIDGE_ROUND_PROMPT_TEMPLATE + HARDENED_PROMPT_SUFFIX + HONEST_BRIDGE_PROMPT_SUFFIX
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
