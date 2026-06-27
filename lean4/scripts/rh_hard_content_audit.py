#!/usr/bin/env python3
"""RHRoute hard-content audit.

Report-only by default. A syntactic gate that lifts the bridge's anti-hollow
discipline (`papers/bedc_mathlib_bridge/scripts/check_no_hollow.py`, Gate H,
token BEDC_GATE_H_HOLLOW_PATTERN) to the RHRoute / zeta / critical-line surface,
so the autonomous pipeline cannot bank typed-but-assumed interfaces as
discharged analytic content.

What it can and cannot do (honest scope):
  * It CAN recognise hollow proof *shapes* from source text: rfl-only,
    True.intro / trivial, a single structure-field projection.
  * It CANNOT decide whether an arbitrary non-hollow proof is analytically
    meaningful. "Not hollow" != "hard analytic content". A list-membership
    bookkeeping lemma and a real ζ estimate both have non-hollow proofs.

Therefore it does NOT auto-credit "hard content". The hard-content ledger is
OPT-IN: a theorem counts only if it carries an explicit

    -- @hard_discharge: <obligation-id>

annotation AND its proof is not hollow. This cannot be gamed by merely writing
a non-hollow-looking proof, and an annotation on a hollow proof is itself an
error.

Signals:
  * VIOLATION  : a declaration whose conclusion uses analytic ζ/RH vocabulary
                 but whose proof is a hollow shape (analytic claim, assumed
                 content). This is the anti-drift trigger.
  * review     : a high-risk declaration whose proof is an existential /
                 anonymous-constructor assembly (e.g. packet repackaging like
                 `zeta_evaluable_to_precision`). Not auto-failed — flagged for
                 human/annotation review, because field-assembly is sometimes
                 legitimate and sometimes vacuous.

Exit status:
  default (report mode):  0 always
  --strict:               1 if any VIOLATION, or any @hard_discharge annotation
                          sits on a hollow proof
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

TOKEN = "BEDC_RH_HARD_CONTENT"
DEFAULT_PATHS = ["lean4/BEDC/Derived/RHRoute"]

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)
BOUNDARY_RE = re.compile(
    r"^\s*(?:@\[|(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|namespace|end|/-)"
)
ANNOT_RE = re.compile(r"--\s*@hard_discharge:\s*(?P<id>[A-Za-z0-9_.\-]+)")

# Substring match (no word boundaries): these tokens occur inside CamelCase
# Lean identifiers (ZetaPrecisionPacket, zetaBall, OnCritLine). `Apart` is
# deliberately excluded — it appears in general `ratApart0` and is not
# ζ-specific.
HIGH_RISK_RE = re.compile(
    r"(?:[Zz]eta|OnCritLine|CritLine|CriticalLine|ApartCrit|"
    r"CritStrip|CriticalStrip|PrimeDefect|PrimeSkew|PrimeNormal|"
    r"FunctionalEquation|RiemannHypothesis|RigidityBoundary|ZeroDecider|"
    r"OffLineZero|NonTrivialZero|NTZero)"
)

HOLLOW_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("true_intro", re.compile(r"^\s*(?:by\s+)?(?:exact\s+)?(?:True\.intro|trivial)\s*$")),
    ("rfl_only", re.compile(r"^\s*(?:by\s+)?(?:exact\s+)?rfl\s*$")),
    ("field_projection", re.compile(
        r"^\s*(?:by\s+)?(?:intro[^\n]*\n\s*)?(?:exact\s+)?"
        r"[A-Za-z_][A-Za-z0-9_'.]*\.[A-Za-z_][A-Za-z0-9_']*\s*$")),
]
EXISTENTIAL_RE = re.compile(r"\b(?:Exists\.intro)\b|⟨")


@dataclass
class Decl:
    path: Path
    line_no: int
    kind: str
    name: str
    signature: str
    proof: str
    discharge_id: str | None


@dataclass
class Report:
    scanned: int = 0
    hollow: list[Decl] = field(default_factory=list)
    ledger: list[Decl] = field(default_factory=list)
    violations: list[tuple[Decl, str]] = field(default_factory=list)
    reviews: list[Decl] = field(default_factory=list)
    bad_annotations: list[tuple[Decl, str]] = field(default_factory=list)


def find_repo_root(start: Path) -> Path:
    for parent in (start, *start.parents):
        if (parent / "lean4" / "lakefile.lean").exists():
            return parent
    raise RuntimeError("cannot locate repo root (lean4/lakefile.lean)")


def parse_decls(path: Path) -> list[Decl]:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    decls: list[Decl] = []
    i = 0
    while i < len(lines):
        m = DECL_RE.match(lines[i])
        if not m:
            i += 1
            continue
        # look back over contiguous comment lines for a discharge annotation
        discharge_id = None
        j = i - 1
        while j >= 0 and (lines[j].lstrip().startswith("--") or lines[j].strip() == ""):
            a = ANNOT_RE.search(lines[j])
            if a:
                discharge_id = a.group("id")
                break
            if lines[j].strip() == "":
                break
            j -= 1
        start = i
        block = [lines[i]]
        i += 1
        while i < len(lines) and not BOUNDARY_RE.match(lines[i]):
            block.append(lines[i])
            i += 1
        sig, _, proof = "\n".join(block).partition(":=")
        decls.append(Decl(path, start + 1, m.group("kind"),
                          m.group("name"), sig.strip(), proof.strip(), discharge_id))
    return decls


def hollow_reason(decl: Decl) -> str | None:
    for label, pat in HOLLOW_PATTERNS:
        if pat.match(decl.proof):
            return label
    return None


def audit(paths: list[Path]) -> Report:
    rep = Report()
    files: list[Path] = []
    for p in paths:
        if p.is_dir():
            files.extend(sorted(p.rglob("*.lean")))
        elif p.suffix == ".lean":
            files.append(p)
    for f in files:
        for decl in parse_decls(f):
            if decl.kind not in ("theorem", "lemma"):
                continue
            rep.scanned += 1
            reason = hollow_reason(decl)
            high_risk = bool(HIGH_RISK_RE.search(decl.signature))
            if reason:
                rep.hollow.append(decl)
                if high_risk:
                    rep.violations.append((decl, reason))
            elif high_risk and EXISTENTIAL_RE.search(decl.proof):
                rep.reviews.append(decl)
            if decl.discharge_id:
                if reason:
                    rep.bad_annotations.append((decl, reason))
                else:
                    rep.ledger.append(decl)
    return rep


def rel(p: Path, root: Path) -> str:
    try:
        return str(p.relative_to(root))
    except ValueError:
        return str(p)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="RHRoute hard-content audit (report-only by default)")
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 on any high-risk hollow violation or hollow @hard_discharge")
    ap.add_argument("--repo-root", default=None)
    args = ap.parse_args(argv)

    root = Path(args.repo_root).resolve() if args.repo_root else find_repo_root(Path.cwd().resolve())
    rep = audit([root / p for p in (args.paths or DEFAULT_PATHS)])

    print(f"[{TOKEN}] RHRoute hard-content audit")
    print(f"  theorems scanned             : {rep.scanned}")
    print(f"  hollow-shaped proofs         : {len(rep.hollow)}")
    print(f"  hard_discharge ledger (opt-in): {len(rep.ledger)}")
    print(f"  high-risk hollow VIOLATIONS  : {len(rep.violations)}")
    print(f"  high-risk existential review : {len(rep.reviews)}")

    if rep.ledger:
        print("\n  hard_discharge ledger (annotated, non-hollow):")
        for d in rep.ledger:
            print(f"    {rel(d.path, root)}:{d.line_no}  {d.name}  <{d.discharge_id}>")
    if rep.violations:
        print("\n  VIOLATIONS (analytic ζ/RH conclusion, hollow proof):")
        for d, why in rep.violations:
            print(f"    {rel(d.path, root)}:{d.line_no}  {d.name}  [{why}]")
    if rep.reviews:
        print("\n  review (high-risk existential/assembly proof — annotate or refute):")
        for d in rep.reviews:
            print(f"    {rel(d.path, root)}:{d.line_no}  {d.name}")
    if rep.bad_annotations:
        print("\n  BAD ANNOTATIONS (@hard_discharge on a hollow proof):")
        for d, why in rep.bad_annotations:
            print(f"    {rel(d.path, root)}:{d.line_no}  {d.name}  [{why}]")

    fail = bool(rep.violations or rep.bad_annotations)
    if args.strict and fail:
        print(f"\n[{TOKEN}] STRICT FAIL: {len(rep.violations)} violation(s), "
              f"{len(rep.bad_annotations)} bad annotation(s)")
        return 1
    print(f"\n[{TOKEN}] report-only OK (use --strict to gate new high-risk hollow claims)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
