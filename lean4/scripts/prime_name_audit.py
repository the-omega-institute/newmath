#!/usr/bin/env python3
"""Prime-in-declaration-name guard for BEDC.

A theorem/lemma/def whose NAME contains a prime (e.g. range'_succ_map) breaks
`bedc_ci.py axiom-purity` #print-axioms parsing, dropping that decl's axiom
result -> "no parsed #print axioms result" -> the pre-merge HARD GATE fails for
EVERY round (observed: 1.5h of 0 Round SUCCESS, see the
feedback_prime_in_decl_name_breaks_axiompurity memory). Lean allows primes in
names, but the axiom-purity tool does not, so BEDC decl names must avoid them
(also matches NAMING.md's no-special-char discipline).

This flags any prime-named declaration under lean4/BEDC. Clean at 0 (the one
historical case, range'_succ_map, was renamed). Informational (exit 0); --strict
exits 1 on any hit, the form a phase_d_lint promotion would take so a prime name
is rejected before it ever lands and breaks the gate.

grep-style walk (fast). os.walk (not rglob).
"""
import argparse
import json
import os
import re
import sys

LEAN_BEDC = "/Users/chronoai/newmath/lean4/BEDC"
# A declaration head whose NAME (not its body / not a reference like List.range')
# contains a prime.
PRIME_DECL_RE = re.compile(
    r"^\s*(?:theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_]*'[A-Za-z0-9_']*)",
    re.MULTILINE,
)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 on any prime-named decl (phase_d-gate form)")
    args = ap.parse_args()
    hits = []
    for root, _d, files in os.walk(LEAN_BEDC, onerror=lambda e: None):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(root, fn)
            try:
                text = open(path, encoding="utf-8").read()
            except OSError:
                continue
            rel = os.path.relpath(path, LEAN_BEDC)
            for m in PRIME_DECL_RE.finditer(text):
                hits.append(f"{rel}::{m.group(1)}")
    out = {
        "scope": "lean4/BEDC declaration names containing a prime",
        "prime_named_decls": len(hits),
        "samples": hits[:30],
        "_note": (
            "A prime in a decl NAME breaks bedc_ci.py axiom-purity #print-axioms "
            "parsing -> pre-merge hard gate fails every round (1.5h stall once). "
            "Fix = rename to drop the prime. 0 = invariant holds. Promote with "
            "--strict in phase_d_lint to reject a prime-named decl before it lands."
        ),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    if args.strict and hits:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
