#!/usr/bin/env python3
"""Hollow-proof / statement-only-avoid-sorry audit for BEDC.

CLAUDE.md §IV explicitly bans the statement-only avoid-sorry idiom: a
`def Foo_Statement : Prop := ∀ …` paired with `theorem Foo_well_formed : True
:= True.intro`, used so a paper `\\leanchecked` can point at it while a
`True.intro` stub pretends the content was kernel-verified -- a hidden-sorry
equivalent. This guard flags that pattern (and bare `_well_formed : True :=
True.intro` stubs that back a verification-sounding name).

A plain `theorem T : True := True.intro` with a `-- TODO:` is an ALLOWED
placeholder (CLAUDE.md §IV), so this only flags the *named-verification* idiom
(`_well_formed` / `_Statement` pairing), not every True.intro.

grep-based (fast, does not time out under load). Informational (exit 0;
--strict exits 1 on any hit for a future hard gate).
"""
import argparse
import json
import os
import re
import sys

LEAN_BEDC = "/Users/chronoai/newmath/lean4/BEDC"
WELLFORMED_STUB_RE = re.compile(
    r"^\s*theorem\s+(\w*(?:_well_formed|_wellformed|_holds|_valid|_checked))\b[^:=]*"
    r":\s*True\s*:=\s*(?:True\.intro|by\s+(?:trivial|exact\s+True\.intro))",
    re.MULTILINE,
)
STATEMENT_DEF_RE = re.compile(r"^\s*def\s+(\w*_[Ss]tatement)\s*:\s*Prop\s*:=", re.MULTILINE)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()
    stub_hits, stmt_hits, paired = [], [], []
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
            stubs = [m.group(1) for m in WELLFORMED_STUB_RE.finditer(text)]
            stmts = [m.group(1) for m in STATEMENT_DEF_RE.finditer(text)]
            for s in stubs:
                stub_hits.append(f"{rel}::{s}")
            for s in stmts:
                stmt_hits.append(f"{rel}::{s}")
            # the banned pairing: a *_Statement def AND a *_well_formed:True stub
            # in the same file is the exact CLAUDE.md §IV hidden-sorry idiom
            if stubs and stmts:
                paired.append(rel)
    out = {
        "scope": "lean4/BEDC (statement-only avoid-sorry idiom, CLAUDE.md §IV)",
        "wellformed_True_stubs": len(stub_hits),
        "statement_prop_defs": len(stmt_hits),
        "banned_pairings_same_file": len(paired),
        "samples_stubs": stub_hits[:20],
        "samples_pairings": paired[:20],
        "_note": (
            "banned_pairings_same_file is the hard signal: a *_Statement def + a "
            "*_well_formed : True := True.intro stub in one file is the exact "
            "hidden-sorry idiom CLAUDE.md §IV forbids (named-def wraps an unproven "
            "hypothesis while True.intro fakes kernel verification). A bare "
            "True.intro placeholder with -- TODO is allowed and not matched here. "
            "0 across all keys = the invariant holds. Informational."
        ),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    if args.strict and paired:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
