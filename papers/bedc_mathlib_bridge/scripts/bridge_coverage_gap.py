#!/usr/bin/env python3
"""Bridge coverage-gap discovery.

Lists BEDC combinatorial / number-theoretic Nat-recursion carriers that are
bridge-shaped (they expose a `def <name> : Nat -> ... -> Nat` structural
recursion, the shape that bridges 0-axiom to a mathlib Nat facade) but are
NOT yet recorded in the bridge MATRIX and are NOT currently being worked by
an open `feat-bridge-<slug>` branch.

This is a READ-ONLY discovery feeder: it produces the prioritized worklist of
un-bridged, un-contested carriers so a bridge author (human or the operator's
feat-bridge PR flow) can pick the next target without colliding with work
already in flight. It never writes a bridge, never touches MATRIX, and never
guesses the mathlib target (the BEDC-carrier -> mathlib-object mapping needs
domain judgement and stays with the author).

Usage:
    python3 scripts/bridge_coverage_gap.py            # human-readable table
    python3 scripts/bridge_coverage_gap.py --json     # machine-readable
    python3 scripts/bridge_coverage_gap.py --top 10   # highest-priority N
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# Combinatorial / number-theoretic carrier keywords. A carrier only enters the
# worklist if its filename stem contains one of these AND it has a Nat->..->Nat
# recursion def; the keyword screen keeps out unrelated *Up carriers (analysis,
# category theory, apophatic refusal packets) whose Nat defs are incidental.
KEYWORDS = (
    "bell", "motzkin", "narayana", "tribonacci", "eulerian", "fusscatalan",
    "catalan", "delannoy", "bernoulli", "stirling", "partition", "lucas",
    "pell", "lah", "hermite", "fibonacci", "pentagon", "hexagon", "pyramid",
    "figurate", "schroder", "fermat", "harmonic", "faulhaber", "genocchi",
    "tangent", "secant", "derangement", "superfactorial", "factorial",
    "binom", "choose", "fuss", "wolstenholme", "overpartition", "euler",
    "central", "triangular", "tetrahedral", "square", "cube", "polygonal",
)

NAT_REC_RE = re.compile(r"def\s+\w+\s*(?:\([^)]*\)\s*)*:\s*Nat\s*(?:->|→)\s*")
# Same shape but capturing the declaration name, so consumers (the bridge
# daemon) get the concrete BEDC.Derived.<Carrier>.<fn> to bridge, not just the
# module. Prefer names ending in a value-word (Number/Count/Value/fn/...) which
# are almost always the closed sequence a mathlib facade corresponds to.
NAT_REC_NAME_RE = re.compile(r"def\s+(\w+)\s*(?:\([^)]*\)\s*)*:\s*Nat\s*(?:->|→)")
# A recurrence / closed-form theorem raises 0-axiom-bridge confidence.
RECUR_THM_RE = re.compile(
    r"\b(?:theorem|lemma)\s+\w*(?:recurrence|succ|closed|closedForm|_eq_|zero|one)\b",
    re.IGNORECASE,
)


def repo_root() -> Path:
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True
    )
    return Path(out.stdout.strip() or ".")


def open_feat_bridge_slugs(root: Path) -> set[str]:
    """Slugs of carriers currently being worked by an open feat-bridge branch.

    We normalise both branch slug and carrier stem to lowercase alnum so
    `feat-bridge-narayana` matches carrier `NarayanaNumberUp`.
    """
    out = subprocess.run(
        ["git", "for-each-ref", "--format=%(refname:short)", "refs/remotes/origin/"],
        capture_output=True,
        text=True,
        cwd=root,
    ).stdout
    slugs: set[str] = set()
    for line in out.splitlines():
        m = re.search(r"feat-bridge-([a-z0-9-]+)", line)
        if m:
            slugs.add(re.sub(r"[^a-z0-9]", "", m.group(1)))
    return slugs


def carrier_contested(stem_norm: str, slugs: set[str]) -> str | None:
    """Return the matching branch slug if this carrier is under active work."""
    for s in slugs:
        # boundary/aggregate branch slugs (e.g. combinatorialboundaries) are
        # skipped as too broad to imply a specific carrier claim.
        if s.endswith("boundaries") or s.endswith("boundary"):
            continue
        core = re.sub(r"(number|numbers|up|poly|polynomial|second|mod|p)$", "", s)
        core = core or s
        if len(core) >= 4 and (stem_norm.startswith(core) or core.startswith(stem_norm[:6])):
            return s
    return None


def carrier_bridged(name: str, matrix: str) -> bool:
    """A carrier is bridged if a MATRIX row cites BEDC.Derived.<name>.<fn>."""
    return f"BEDC.Derived.{name}." in matrix


def scan(root: Path):
    derived = root / "lean4" / "BEDC" / "Derived"
    matrix = (root / "papers" / "bedc_mathlib_bridge" / "MATRIX.md").read_text()
    slugs = open_feat_bridge_slugs(root)

    total = bridged = contested = 0
    worklist = []
    for f in sorted(derived.glob("*Up.lean")):
        name = f.stem  # e.g. NarayanaNumberUp
        stem_norm = re.sub(r"[^a-z0-9]", "", name[:-2].lower())
        if not any(k in stem_norm for k in KEYWORDS):
            continue
        text = f.read_text()
        if not NAT_REC_RE.search(text):
            continue
        total += 1
        if carrier_bridged(name, matrix):
            bridged += 1
            continue
        claim = carrier_contested(stem_norm, slugs)
        if claim:
            contested += 1
            continue
        # priority: a closed-form/recurrence theorem cluster makes a clean
        # 0-axiom bridge far more likely, so rank those first.
        nat_defs = len(NAT_REC_RE.findall(text))
        has_recur = bool(RECUR_THM_RE.search(text))
        priority = (2 if has_recur else 0) + min(nat_defs, 3)
        # Concrete bridgeable declarations. Rank value-word-suffixed names first
        # (Number/Count/Value/Term/fn) — those are the closed forms a mathlib
        # facade lines up with; a bare helper like `step` rarely bridges.
        names = NAT_REC_NAME_RE.findall(text)
        seen: set[str] = set()
        ordered = [n for n in names if not (n in seen or seen.add(n))]
        # Rank the PRIMARY closed sequence/count function first, demoting
        # internal helpers (prefix-sum / fuel-bounded / step / layer / raw
        # accumulators) that never line up with a mathlib facade. A worker fed a
        # helper as its anchor either bridges nothing or the wrong thing.
        value_words = ("Number", "Count", "Value", "Term", "fn", "Fn")
        helper_words = (
            "Prefix", "Step", "Fuel", "Layer", "Row", "Raw", "raw", "Seq",
            "Aux", "Acc", "Helper", "List", "Tail", "Drop", "Fold", "Loop",
        )

        def rank(n: str) -> tuple[int, int]:
            is_helper = 1 if n.endswith(helper_words) else 0
            is_value = 0 if n.endswith(value_words) else 1
            return (is_helper, is_value)

        ordered.sort(key=rank)
        namespace = f"BEDC.Derived.{name}"
        bridge_decls = [f"{namespace}.{n}" for n in ordered[:4]]
        worklist.append(
            {
                "carrier": name,
                "namespace": namespace,
                "bridge_decls": bridge_decls,
                "file": str(f.relative_to(root)),
                "nat_recursion_defs": nat_defs,
                "has_recurrence_or_closedform_theorem": has_recur,
                "priority": priority,
            }
        )
    worklist.sort(key=lambda d: (-d["priority"], d["carrier"]))
    return {
        "total_bridge_shaped_carriers": total,
        "already_in_matrix": bridged,
        "contested_open_feat_bridge": contested,
        "uncontested_unbridged": len(worklist),
        "worklist": worklist,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--top", type=int, default=0, help="only the highest-priority N")
    args = ap.parse_args()

    result = scan(repo_root())
    if args.top:
        result["worklist"] = result["worklist"][: args.top]

    if args.json:
        print(json.dumps(result, indent=2))
        return 0

    print(
        f"bridge coverage gap: {result['total_bridge_shaped_carriers']} "
        f"bridge-shaped combinatorial carriers | "
        f"{result['already_in_matrix']} bridged | "
        f"{result['contested_open_feat_bridge']} contested (open feat-bridge) | "
        f"{result['uncontested_unbridged']} uncontested-unbridged worklist"
    )
    for row in result["worklist"]:
        flag = "recur" if row["has_recurrence_or_closedform_theorem"] else "     "
        print(
            f"  p{row['priority']} [{flag}] {row['carrier']:34} "
            f"({row['nat_recursion_defs']} Nat-rec defs)"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
