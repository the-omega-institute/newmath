#!/usr/bin/env python3
"""
Audit lean4/BEDC/ for axiom declarations.

BEDC project policy: lean4/BEDC/ forbids `axiom` entirely. Primitives are
encoded as `inductive` types, `def` definitions, or `class`/`structure`
setup fields. See CLAUDE.md / AGENTS.md "Lean 4 形式化纪律".

This script enforces the policy mechanically: it scans lean4/BEDC/**/*.lean
for any `axiom` declaration and exits non-zero if any are found.

Exit codes:
  0  no axioms (project invariant holds)
  1  one or more axioms found (policy violation)
  2  setup error (lean4/BEDC/ missing, etc.)

Usage:
  python3 tools/check-axioms.py [--repo-root PATH] [--json]

Default --repo-root is the parent of the script's directory.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass
class Axiom:
    name: str
    signature: str
    source_path: str
    line: int


NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)
AXIOM_RE = re.compile(r"^axiom\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+?)\s*$", re.MULTILINE)


def collect_source_axioms(repo_root: Path) -> list[Axiom]:
    """Walk lean4/BEDC/ and return every `axiom` declaration with its qualified name."""
    out: list[Axiom] = []
    bedc_root = repo_root / "lean4" / "BEDC"
    if not bedc_root.exists():
        raise FileNotFoundError(f"lean4/BEDC/ not found at {bedc_root}")
    for path in sorted(bedc_root.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        ns_match = NAMESPACE_RE.search(text)
        ns = ns_match.group(1) if ns_match else ""
        for m in AXIOM_RE.finditer(text):
            name = m.group(1)
            sig = m.group(2).strip()
            qualified = f"{ns}.{name}" if ns else name
            line_no = text.count("\n", 0, m.start()) + 1
            rel = path.relative_to(repo_root / "lean4" / "BEDC").as_posix()
            out.append(Axiom(name=qualified, signature=sig, source_path=rel, line=line_no))
    return out


def format_human(axioms: list[Axiom]) -> str:
    if not axioms:
        return "Axiom audit: 0 axioms in lean4/BEDC/. Project invariant holds."

    lines: list[str] = []
    lines.append(f"Axiom audit: FAIL — {len(axioms)} axiom declaration(s) found.")
    lines.append("BEDC project policy: lean4/BEDC/ forbids ALL axioms (see CLAUDE.md / AGENTS.md).")
    lines.append("")
    for ax in axioms:
        lines.append(f"  {ax.name}  ({ax.source_path}:{ax.line})  : {ax.signature}")
    lines.append("")
    lines.append("Action: encode the primitive as `inductive`, `def`, or `class`/`structure` field.")
    lines.append("Decision tree:")
    lines.append("  closed-generation finite constructors  →  inductive")
    lines.append("  derivable from existing definitions    →  def")
    lines.append("  truly abstract carrier (parametric)    →  class/structure setup field")
    lines.append("  none of the above                      →  redesign the interface; do NOT add axiom")
    return "\n".join(lines)


def format_json(axioms: list[Axiom]) -> str:
    payload = {
        "passed": len(axioms) == 0,
        "axiom_count": len(axioms),
        "axioms": [
            {"name": a.name, "signature": a.signature, "source_path": a.source_path, "line": a.line}
            for a in axioms
        ],
    }
    return json.dumps(payload, indent=2)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Enforce BEDC zero-axiom policy in lean4/BEDC/."
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    parser.add_argument("--json", action="store_true", help="emit JSON to stdout")
    args = parser.parse_args()

    try:
        axioms = collect_source_axioms(args.repo_root)
    except FileNotFoundError as exc:
        print(f"setup error: {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(format_json(axioms))
    else:
        print(format_human(axioms), file=sys.stderr if axioms else sys.stdout)
    return 0 if not axioms else 1


if __name__ == "__main__":
    sys.exit(main())
