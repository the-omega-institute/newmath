#!/usr/bin/env python3
"""Bridge coverage-gap discovery for BEDC Nat-value sequence carriers.

Lists BEDC.Derived carriers with Nat-valued source functions and local
recurrence / closed-form theorem signals.

This script reports the coverage tail. A Nat-valued row is only honest as a
pointwise/readback equality over an existing BEDC.Derived source; it is not a
carrier equivalence. Consumers that need mathlib target hints can use
`bridge_nat_sequence_candidates.py`.

It never writes a bridge and never touches MATRIX.

Usage:
    python3 scripts/bridge_coverage_gap.py            # human-readable table
    python3 scripts/bridge_coverage_gap.py --json     # machine-readable
    python3 scripts/bridge_coverage_gap.py --top 10   # highest-priority N
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Stem blacklist for carriers whose Nat declarations are auxiliary packet,
# apophatic, or analysis bookkeeping data rather than Nat sequence surfaces.
EXCLUDED_STEM_TERMS = (
    "namecert",
    "refusal",
    "apophatic",
    "seal",
    "askpolicy",
    "descentcert",
    "socket",
    "metric",
    "space",
    "uniform",
    "modulus",
    "budget",
    "synchronizer",
    "baire",
    "cantor",
    "hilleyosida",
    "cauchyseal",
    "contfrac",
    "trajectory",
)

DECL_HEADER_RE = re.compile(
    r"(?ms)^\s*def\s+([A-Za-z_][A-Za-z0-9_']*)\b(.*?)(?::=|\n\s*\|)"
)
# A recurrence / closed-form theorem raises bridge confidence.
RECUR_THM_RE = re.compile(
    r"\b(?:theorem|lemma)\s+\w*(?:recurrence|recursion|succ|successor|closed|closedForm|closed_form|closedFormula|closed_formula|formula|_eq_|zero|one|boundary|spec|pascal|choose|factorial)\b",
    re.IGNORECASE,
)
NON_NAT_INPUT_TERMS = (
    "BHist",
    "List",
    "Bool",
    "Int",
    "IntegerUp",
    "Prop",
    "Option",
    "GoldenPhiPair",
    "Z",
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


def carrier_excluded(stem_norm: str) -> bool:
    return any(term in stem_norm for term in EXCLUDED_STEM_TERMS)


def _last_top_level_colon(text: str) -> int:
    depth = 0
    found = -1
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            found = index
    return found


def _pure_nat_type(prefix: str, typ: str) -> bool:
    if any(term in prefix for term in NON_NAT_INPUT_TERMS):
        return False
    clean = " ".join(typ.replace("→", "->").split())
    parts = [part.strip(" ()") for part in clean.split("->")]
    return bool(parts) and all(part == "Nat" for part in parts)


def _pure_nat_value_decl(header: str) -> bool:
    colon = _last_top_level_colon(header)
    if colon < 0:
        return False
    prefix = header[:colon]
    typ = header[colon + 1 :]
    return _pure_nat_type(prefix, typ)


def pure_nat_value_decl_names(text: str) -> list[str]:
    names: list[str] = []
    for match in DECL_HEADER_RE.finditer(text):
        if _pure_nat_value_decl(match.group(2)):
            names.append(match.group(1))
    return names


VALUE_WORDS = ("Number", "Count", "Value", "Term", "fn", "Fn")
HELPER_WORDS = (
    "Prefix", "Step", "Fuel", "Layer", "Row", "Raw", "raw", "Seq",
    "Aux", "Acc", "Helper", "List", "Tail", "Drop", "Fold", "Loop",
)


def order_decl_names(names: list[str]) -> list[str]:
    seen: set[str] = set()
    ordered = [n for n in names if not (n in seen or seen.add(n))]

    def rank(n: str) -> tuple[int, int, int, str]:
        is_helper = 1 if n.endswith(HELPER_WORDS) else 0
        is_value = 0 if n.endswith(VALUE_WORDS) else 1
        return (is_helper, is_value, len(n), n)

    return sorted(ordered, key=rank)


def scan(root: Path):
    derived = root / "lean4" / "BEDC" / "Derived"
    matrix = (root / "papers" / "bedc_mathlib_bridge" / "MATRIX.md").read_text()
    slugs = open_feat_bridge_slugs(root)

    total = bridged = contested = excluded = no_theorem_signal = 0
    worklist = []
    for f in sorted(derived.glob("*Up.lean")):
        name = f.stem  # e.g. NarayanaNumberUp
        stem_norm = re.sub(r"[^a-z0-9]", "", name[:-2].lower())
        if carrier_excluded(stem_norm):
            excluded += 1
            continue
        text = f.read_text()
        names = pure_nat_value_decl_names(text)
        if not names:
            continue
        has_recur = bool(RECUR_THM_RE.search(text))
        if not has_recur:
            no_theorem_signal += 1
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
        nat_defs = len(names)
        priority = (2 if has_recur else 0) + min(nat_defs, 3)
        # Demote carriers whose mathlib counterpart is Rat- or Finset-valued
        # (Bernoulli/Euler polynomials, harmonic numbers, set-partition/Bell
        # counts, generating-function objects): those can't be an exported_core
        # 0-axiom bridge and always fail-close, so a bridge consumer should try
        # the Nat-closed-form carriers (Catalan/central-factorial/Lah/figurate/
        # ...) first, which have a real chance of a clean Nat facade.
        RAT_FINSET_HARD = (
            "Bernoulli", "Euler", "Bell", "Genocchi", "Tangent", "Secant",
            "Poly", "Partition", "Overpartition", "Umbral", "Faulhaber",
            "Harmonic", "Hyperharmonic", "Hermite",
        )
        if any(k in name for k in RAT_FINSET_HARD):
            priority -= 5
        ordered = order_decl_names(names)
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
        "class": "nat_sequence_coverage_gap",
        "structural_candidate": False,
        "allowed_bridge_kind": "nat_value_sequence",
        "note": "Nat-valued carriers are eligible only as honest pointwise/readback bridges.",
        "total_bridge_shaped_carriers": total,
        "already_in_matrix": bridged,
        "contested_open_feat_bridge": contested,
        "excluded_by_stem_blacklist": excluded,
        "without_recurrence_or_closedform_signal": no_theorem_signal,
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
        f"bridge-shaped Nat-value sequence carriers | "
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
