#!/usr/bin/env python3
"""RH-lane pre-landing gate suite.

Learned from loning's bedc_mathlib_bridge pipeline (ring-bundle audit +
axiom guards) plus the incidents this lane actually hit: worker-introduced
ratRing bundle duplicates, workers editing loning's shared substrate /
the bridge manifest, and propext leaks. Run this on a worktree BEFORE
pushing an RH-lane brick to feat, so a bad brick never reaches the rollup.

Gates (each fails the run; --gate to select a subset):
  scope    : the diff (base..HEAD) touches ONLY RH-lane-owned paths. Editing
             papers/bedc_mathlib_bridge, .github, the bio main tree, or
             loning's IntervalMatrixPSD is flagged (allow the last with
             --allow-substrate for a sanctioned dedup).
  ringbundle: loning's check_ring_bundle.py reports 0 duplicate RelCommRing
             bundles (catches worker-added ratRing copies before they turn
             the rollup's bridge-build red).
  purity   : bedc_ci.py axiom-purity --strict reports impure=0 (no
             propext / Classical.choice / Quot.sound).
  atlas    : rh_route_atlas_check.py structural pass.

Usage: run from the worktree root.
  python3 tools/rh_lane_preflight.py --base origin/feat/rh-route-deepening
  python3 tools/rh_lane_preflight.py --gate scope,ringbundle   # subset
  python3 tools/rh_lane_preflight.py --allow-substrate         # sanctioned IntervalMatrixPSD edit

Exit 0 iff every selected gate passes.
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

# Paths an RH-lane brick is allowed to change. Anything outside is flagged by `scope`.
ALLOWED_PREFIXES = (
    "lean4/BEDC/Derived/RHRoute/",
    "lean4/BEDC.lean",
    "papers/bedc/parts/visions/rh/",
    "tools/rh_route_atlas_check.py",
    "tools/rh_lane_preflight.py",
)
# Never-touch (hard fail even with --allow-substrate).
FORBIDDEN_PREFIXES = (
    "papers/bedc_mathlib_bridge/",   # ElonSG's bridge (incl. the canonical manifest) — read-only
    ".github/",                       # CI workflows — off-limits
)
# loning's shared archimedean substrate — allowed only for a sanctioned dedup (--allow-substrate).
SUBSTRATE_PREFIX = "lean4/BEDC/Derived/RHRoute/IntervalMatrixPSD/"


def run(cmd: list[str], cwd: Path) -> tuple[int, str]:
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def repo_root(start: Path) -> Path:
    for c in [start, *start.parents]:
        if (c / "lean4").is_dir() and (c / "papers").is_dir():
            return c
    return start


def gate_scope(root: Path, base: str, allow_substrate: bool) -> list[str]:
    rc, out = run(["git", "diff", "--name-only", f"{base}..HEAD"], root)
    if rc != 0:
        return [f"scope: git diff failed ({out.strip()[:120]})"]
    errs = []
    for f in [l.strip() for l in out.splitlines() if l.strip()]:
        if any(f.startswith(p) for p in FORBIDDEN_PREFIXES):
            errs.append(f"scope: touches FORBIDDEN path {f}")
        elif f.startswith(SUBSTRATE_PREFIX):
            if not allow_substrate:
                errs.append(f"scope: touches loning substrate {f} (use --allow-substrate only for a sanctioned dedup)")
        elif not any(f.startswith(p) for p in ALLOWED_PREFIXES):
            errs.append(f"scope: touches non-RH-lane path {f}")
    return errs


def gate_ringbundle(root: Path) -> list[str]:
    script = root / "papers/bedc_mathlib_bridge/scripts/check_ring_bundle.py"
    if not script.exists():
        return ["ringbundle: check_ring_bundle.py not found"]
    rc, out = run(["python3", str(script)], root)
    if rc == 0 and "FAIL" not in out:
        return []
    tail = out.strip().splitlines()[-1] if out.strip() else "(no output)"
    return [f"ringbundle: {tail}"]


def gate_purity(root: Path) -> list[str]:
    script = root / "lean4/scripts/bedc_ci.py"
    if not script.exists():
        return ["purity: bedc_ci.py not found"]
    rc, out = run(["python3", str(script), "axiom-purity", "--strict"], root)
    if "impure=0" in out and "FAIL" not in out:
        return []
    line = next((l for l in out.splitlines() if "impure=" in l), out.strip()[:160])
    return [f"purity: {line.strip()}"]


def gate_atlas(root: Path) -> list[str]:
    script = root / "tools/rh_route_atlas_check.py"
    if not script.exists():
        return []  # atlas checker optional
    rc, out = run(["python3", str(script)], root)
    if rc == 0:
        return []
    return [f"atlas: {out.strip().splitlines()[-1] if out.strip() else 'failed'}"]


GATES = {
    "scope": gate_scope,
    "ringbundle": gate_ringbundle,
    "purity": gate_purity,
    "atlas": gate_atlas,
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="origin/feat/rh-route-deepening")
    ap.add_argument("--gate", default="scope,ringbundle,purity,atlas")
    ap.add_argument("--allow-substrate", action="store_true")
    args = ap.parse_args()

    root = repo_root(Path.cwd())
    selected = [g.strip() for g in args.gate.split(",") if g.strip()]
    all_errs: list[str] = []
    for name in selected:
        fn = GATES.get(name)
        if fn is None:
            all_errs.append(f"{name}: unknown gate")
            continue
        errs = fn(root, args.base, args.allow_substrate) if name == "scope" else fn(root)
        if errs:
            all_errs.extend(errs)
            print(f"[preflight] {name}: FAIL")
        else:
            print(f"[preflight] {name}: ok")

    if all_errs:
        print(f"\n[preflight] FAIL ({len(all_errs)} issue(s)):")
        for e in all_errs:
            print(f"  - {e}")
        return 1
    print("\n[preflight] OK: all gates passed; brick is safe to land")
    return 0


if __name__ == "__main__":
    sys.exit(main())
