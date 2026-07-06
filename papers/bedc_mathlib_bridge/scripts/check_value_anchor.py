#!/usr/bin/env python3
"""Dead-anchor gate for exported_core bridge rows.

This script rejects only the direct dead-anchor shape: a BHist wrapper whose
body is just an observer/reifier round-trip around a native Nat function, with
no semantic BEDC theorem doing work. It does not reject ordinary Nat-valued
BEDC.Derived sequences merely because their target is a Nat declaration.

Deterministic reject pattern. A carrier's Lean source is a dead anchor when all
three roles co-occur in one BHist-typed wrapper def:

  observer   : bwordLength / toNat / eval-like  (BHist -> Nat)
  reifier    : natToUnary / ofNat / encode-like (Nat  -> BHist)
  native core: a plain `Nat -> ... -> Nat` recursion (the real math)

i.e. `def <X>Fn (... : BHist ...) : BHist := <reifier> (<natCore> (<observer> ...) ...)`.
Full "does this anchor carry content" is undecidable in general; this catches
the KNOWN laundering shape deterministically. Anything else stays review-gated
(this gate never advertises itself as a proof of semantic honesty).

Because a carrier's wrapper may live in a DIFFERENT file from the carrier's own
module (e.g. BinomialIdentitiesUp.C delegates to PochhammerUp.natChooseCount ->
FactorialUp.natChooseFn), the scan follows the delegation by name across all of
lean4/BEDC/Derived, not just the carrier's own file.

Modes:
  (default) : report findings, exit 0 (shadow report)
  --gate    : exit 1 if any exported_core row is dead-anchor laundering
  --decl D  : classify a single decl (for the per-bridge heavy-check gate)
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

OBSERVER = ("bwordLength", "toNat", "bwordValue")
REIFIER = ("natToUnary", "ofNat")
# the laundering wrapper: BHist-typed def whose body is reifier(core(observer ...))
LAUNDER_FN_RE = re.compile(
    r"def\s+(\w+)\s*\([^)]*:\s*BHist[^)]*\)\s*:\s*(?:BHist|Nat)\s*:=\s*"
    r"(?:bwordLength\s*\(\s*)?"
    r"(natToUnary|ofNat)\s*\(\s*(\w+)\s*\(\s*(?:bwordLength|toNat)",
    re.MULTILINE,
)
# plain Nat-native recursion `def f : Nat -> ... -> Nat`
NAT_NATIVE_RE = re.compile(r"def\s+(\w+)\s*(?:\([^)]*\)\s*)*:\s*Nat\s*(?:->|→)")
SEMANTIC_THEOREM_RE = re.compile(
    r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*"
    r"(?:pascal|recurrence|succ|closed|closedForm|_eq_|zero|one|boundary|spec|choose|factorial)"
    r"[A-Za-z0-9_']*)\b(.*?)(?=\n\s*\n|\n\s*(?:def |theorem |abbrev |lemma )|\Z)",
    re.DOTALL | re.IGNORECASE,
)


def repo_root() -> Path:
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True
    )
    return Path(out.stdout.strip() or ".")


def _derived_sources(root: Path):
    d = root / "lean4" / "BEDC" / "Derived"
    out = []
    for f in sorted(d.rglob("*.lean")):
        try:
            out.append((f, f.read_text()))
        except Exception:
            continue
    return out


def _laundering_wrappers(sources):
    """Set of wrapper Fn names + Nat-native core names in the whole Derived tree.

    A wrapper is `def <X>Fn (... BHist ...) : BHist|Nat := <reifier> (<core>
    (<observer> ...) ...)`. Core names shorter than 4 chars are dropped to avoid
    ambiguous single-letter matches."""
    wrappers: set[str] = set()
    cores: set[str] = set()
    for _f, text in sources:
        for m in LAUNDER_FN_RE.finditer(text):
            wrapper, _reifier, core = m.group(1), m.group(2), m.group(3)
            wrappers.add(wrapper)
            if len(core) >= 4:
                cores.add(core)
    return wrappers, cores


def _module_text(root: Path, bedc_decl: str, sources) -> str:
    parts = bedc_decl.split(".")
    if len(parts) >= 4 and parts[0] == "BEDC" and parts[1] == "Derived":
        expected = root / "lean4" / "BEDC" / "Derived" / f"{parts[2]}.lean"
        for path, text in sources:
            if path == expected:
                return text
    module = ".".join(parts[:-1])
    needle = f"namespace {module}"
    for _path, text in sources:
        if needle in text:
            return text
    return ""


def _has_semantic_theorem(root: Path, bedc_decl: str, sources) -> bool:
    short = bedc_decl.split(".")[-1]
    text = _module_text(root, bedc_decl, sources)
    if not text:
        return False
    for match in SEMANTIC_THEOREM_RE.finditer(text):
        theorem_name = match.group(1)
        theorem_block = match.group(0)
        if short in theorem_name or re.search(r"\b" + re.escape(short) + r"\b", theorem_block):
            return True
    return False


def classify_decl(root: Path, bedc_decl: str, sources) -> dict:
    """Classify a BEDC.Derived.* decl as dead_anchor / structural / unknown.

    PRECISE text-layer detector for the DIRECT laundering shape (a carrier whose
    own module, or a module it names directly, defines the observer/reifier/core
    round-trip wrapper). Deep multi-hop delegation that crosses several unrelated
    modules is intentionally NOT chased here (text parsing over-matches and
    false-positives); that case is the job of the authoritative Lean-env gate
    (BridgeAudit.lean). This detector is a shadow / first-line signal, never a
    proof of semantic honesty."""
    short = bedc_decl.split(".")[-1]
    wrappers, _cores = _laundering_wrappers(sources)
    struct_re = re.compile(r"(?:structure|inductive)\s+" + re.escape(short) + r"\b")
    is_structure = any(struct_re.search(t) for _f, t in sources)
    reasons = []
    # the carrier's own def body directly names a laundering wrapper/core or
    # exhibits the observer+reifier round-trip in one place.
    body_re = re.compile(
        r"(?:abbrev|def)\s+" + re.escape(short) + r"\b.*?:=\s*(.*?)(?=\n\s*\n|\n\s*(?:def |theorem |abbrev |lemma )|\Z)",
        re.DOTALL,
    )
    for _f, text in sources:
        m = body_re.search(text)
        if not m:
            continue
        body = " ".join(m.group(1).split())[:400]
        if "bwordLength" in body and "natToUnary" in body:
            reasons.append("DeadAnchor:bwordLength_natToUnary_roundtrip")
        for w in wrappers:
            if re.search(r"\b" + re.escape(w) + r"\b", body):
                reasons.append(f"DelegatesToLaunderingWrapper:{w}")
        break
    reasons = sorted(set(reasons))
    if reasons and not is_structure:
        if _has_semantic_theorem(root, bedc_decl, sources):
            return {
                "decl": bedc_decl,
                "kind": "nat_value_sequence_or_unknown",
                "eligible": True,
                "reasons": ["DirectWrapperButSemanticTheoremPresent"],
            }
        return {"decl": bedc_decl, "kind": "dead_anchor", "eligible": False, "reasons": reasons[:6]}
    if is_structure:
        return {"decl": bedc_decl, "kind": "structural_carrier", "eligible": True,
                "reasons": ["StructureOrInductiveCarrier"]}
    return {"decl": bedc_decl, "kind": "nat_value_sequence_or_unknown", "eligible": True, "reasons": ["NoDirectDeadAnchor"]}


def exported_core_rows(matrix_path: Path) -> list:
    rows = []
    for line in matrix_path.read_text().splitlines():
        m = re.search(r"bedc-bridge-row:\s*(\{.*\})\s*-->", line)
        if not m:
            continue
        try:
            row = json.loads(m.group(1))
        except Exception:
            continue
        if row.get("kind") == "exported_core":
            rows.append(row)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("matrix", nargs="?", default="MATRIX.md")
    ap.add_argument("--gate", action="store_true", help="exit 1 on any dead anchor")
    ap.add_argument("--decl", help="classify a single BEDC.Derived.* decl and exit")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    root = repo_root()
    sources = _derived_sources(root)

    if args.decl:
        res = classify_decl(root, args.decl, sources)
        print(json.dumps(res, indent=2))
        return 0 if res["eligible"] else 1

    matrix_path = Path(args.matrix)
    if not matrix_path.is_absolute():
        matrix_path = root / "papers" / "bedc_mathlib_bridge" / matrix_path
    rows = exported_core_rows(matrix_path)
    flagged = []
    for row in rows:
        decl = row.get("bedc_irreducible_decl", "")
        if not decl.startswith("BEDC.Derived."):
            continue
        res = classify_decl(root, decl, sources)
        if res["kind"] == "dead_anchor":
            flagged.append({**res, "row_id": row.get("row_id"), "mathlib_decl": row.get("mathlib_decl")})

    if args.json:
        print(json.dumps({"exported_core": len(rows), "dead_anchor": flagged}, indent=2))
    else:
        print(f"[check-value-anchor] exported_core={len(rows)} dead-anchor={len(flagged)}")
        for x in flagged:
            print(f"  DEAD_ANCHOR {x['row_id']}: {x['decl']} = {x['mathlib_decl']}  {x['reasons']}")

    if args.gate and flagged:
        print(f"[check-value-anchor] GATE FAIL (BEDC_GATE_N_NAT_SHADOW_LAUNDERING): {len(flagged)} row(s)")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
