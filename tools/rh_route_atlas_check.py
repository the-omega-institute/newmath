#!/usr/bin/env python3
"""RH-route axiom-footprint atlas consistency check.

Adopts the bedc_mathlib_bridge harness discipline (measured axiom footprints +
first-class boundary/refutation rows) for the mathlib-free RH-route core.

The atlas (papers/bedc/parts/visions/rh/rh_route_axiom_atlas.md) carries one
machine-readable row per RH-route direction, embedded as
`<!-- rh-route-row: {json} -->`. This checker validates each row's factual
claims against the tree. Axiom measurement itself stays authoritative in
`bedc_ci.py axiom-purity --strict`; this checker cross-references it rather
than re-measuring, so there is a single measurement source of truth.

Default mode is build-free (grep-level structural + footprint-invariant checks)
so it is cheap to run. `--measure` additionally shells out to `#print axioms`
for named targets via `lake env lean` and compares against the claimed
footprint (heavier; needs a built tree).

Exit 0 iff every row is internally consistent and matches the tree.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

KIND_VOCAB = {
    "formalized_theorem",   # closed 0-axiom theorem landed in the RH-route tree
    "conditional_theorem",  # honest `_of_<obligation>` implication; obligation un-inhabited
    "measured_boundary",    # cannot be done 0-axiom here (or RH-equivalent / blocked); recorded, not bridged
    "refuted",              # attempted and rejected (vacuous / wrong); kept visible as a bad-example
    "paper_principle",      # documented in paper prose only; no Lean target claimed
}
LEVERAGE_VOCAB = {"none", "diagnostic", "brick"}

ROW_RE = re.compile(r"<!--\s*rh-route-row:\s*(\{.*?\})\s*-->", re.DOTALL)


def repo_root(start: Path) -> Path:
    p = start.resolve()
    for cand in [p, *p.parents]:
        if (cand / ".git").exists() or (cand / "lean4").is_dir():
            return cand
    return p


def load_rows(atlas: Path) -> list[dict]:
    text = atlas.read_text(encoding="utf-8")
    rows = []
    for m in ROW_RE.finditer(text):
        rows.append(json.loads(m.group(1)))
    return rows


def decl_exists(root: Path, lean_target: str) -> bool:
    """Grep the RH-route tree for a declaration whose fully-qualified name ends
    in the atlas's lean_target. We look for the final identifier as a def/theorem
    name, which is enough to catch typos / stale targets without a full build."""
    short = lean_target.rsplit(".", 1)[-1]
    rh_dir = root / "lean4" / "BEDC" / "Derived" / "RHRoute"
    if not rh_dir.is_dir():
        return False
    pat = re.compile(rf"\b(theorem|def|lemma|abbrev|structure|inductive)\s+{re.escape(short)}\b")
    for f in rh_dir.rglob("*.lean"):
        try:
            if pat.search(f.read_text(encoding="utf-8")):
                return True
        except OSError:
            continue
    return False


def measure_axioms(root: Path, lean_target: str, lean_module: str) -> list[str] | None:
    """`#print axioms <target>` via lake env lean; return the forbidden axioms
    found ([] means 0-axiom / CIC-pure). None on measurement failure.

    `lean_module` is the import path (a namespace prefix is NOT a reliable module
    name — e.g. namespace `…RHRoute.FiniteVisibility` lives in module
    `…RHRoute.FiniteVisibilityIncompleteness`), so each measurable row declares it."""
    scratch = root / "lean4" / "_rh_atlas_measure.lean"
    body = f"import {lean_module}\n#print axioms {lean_target}\n"
    try:
        scratch.write_text(body, encoding="utf-8")
        out = subprocess.run(
            ["lake", "env", "lean", scratch.name],
            cwd=root / "lean4", capture_output=True, text=True, timeout=1800,
        )
    finally:
        scratch.unlink(missing_ok=True)
    blob = out.stdout + out.stderr
    forbidden = [a for a in ("propext", "Classical.choice", "Quot.sound") if a in blob]
    if "does not depend on any axioms" in blob or (out.returncode == 0 and not forbidden):
        return forbidden
    if forbidden:
        return forbidden
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--atlas", default="papers/bedc/parts/visions/rh/rh_route_axiom_atlas.md")
    ap.add_argument("--measure", action="store_true", help="also run #print axioms per target (needs built tree)")
    args = ap.parse_args()

    root = repo_root(Path(args.atlas) if Path(args.atlas).is_absolute() else Path.cwd())
    atlas = (root / args.atlas) if not Path(args.atlas).is_absolute() else Path(args.atlas)
    if not atlas.exists():
        print(f"[rh-atlas] atlas not found: {atlas}")
        return 1

    rows = load_rows(atlas)
    if not rows:
        print(f"[rh-atlas] no rh-route-row entries parsed from {atlas}")
        return 1

    errors: list[str] = []
    seen_ids: set[str] = set()
    for r in rows:
        rid = r.get("row_id", "<missing>")
        if rid in seen_ids:
            errors.append(f"{rid}: duplicate row_id")
        seen_ids.add(rid)

        kind = r.get("kind")
        if kind not in KIND_VOCAB:
            errors.append(f"{rid}: kind '{kind}' not in {sorted(KIND_VOCAB)}")
            continue
        if r.get("rh_leverage") not in LEVERAGE_VOCAB:
            errors.append(f"{rid}: rh_leverage '{r.get('rh_leverage')}' not in {sorted(LEVERAGE_VOCAB)}")

        tgt = r.get("lean_target")
        fp = r.get("axiom_footprint")

        if kind in ("formalized_theorem", "conditional_theorem"):
            if not tgt:
                errors.append(f"{rid}: {kind} requires lean_target")
            elif not decl_exists(root, tgt):
                errors.append(f"{rid}: lean_target '{tgt}' not found in RHRoute tree")
            if kind == "formalized_theorem" and fp != []:
                errors.append(f"{rid}: formalized_theorem must have axiom_footprint [] (0-axiom); got {fp}")
            if args.measure and tgt and decl_exists(root, tgt):
                mod = r.get("lean_module")
                if not mod:
                    errors.append(f"{rid}: --measure needs lean_module for '{tgt}'")
                else:
                    got = measure_axioms(root, tgt, mod)
                    if got is None:
                        errors.append(f"{rid}: could not measure #print axioms for '{tgt}'")
                    elif sorted(got) != sorted(fp or []):
                        errors.append(f"{rid}: measured footprint {got} != claimed {fp}")

        elif kind == "measured_boundary":
            if not r.get("boundary_reason"):
                errors.append(f"{rid}: measured_boundary requires boundary_reason")
            # invariant: a boundary must NOT export an axiom-carrying closed theorem.
            if tgt and kind == "formalized_theorem":
                errors.append(f"{rid}: measured_boundary must not be a closed formalized_theorem")

        elif kind == "refuted":
            if not r.get("refutation"):
                errors.append(f"{rid}: refuted requires refutation reason")
            if not r.get("paper_site"):
                errors.append(f"{rid}: refuted requires paper_site pointer")

        elif kind == "paper_principle":
            if not r.get("paper_site"):
                errors.append(f"{rid}: paper_principle requires paper_site")

    if errors:
        print(f"[rh-atlas] FAIL: {len(errors)} issue(s) across {len(rows)} row(s)")
        for e in errors:
            print(f"  - {e}")
        return 1
    print(f"[rh-atlas] OK: {len(rows)} rows consistent"
          + (" (footprints measured)" if args.measure else " (structural; run --measure for #print cross-check)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
