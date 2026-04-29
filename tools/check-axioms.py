#!/usr/bin/env python3
"""
Audit lean4/BEDC/ axiom declarations against lean4/AXIOMS.md registry.

Exit codes:
  0  parity (every source axiom is registered, every registered axiom exists in source)
  1  divergence (unregistered axioms in source, OR registered-but-missing in source)
  2  setup error (registry parse failure, source-tree missing, etc.)

Usage:
  python3 tools/check-axioms.py [--repo-root PATH] [--json]

Default --repo-root is the parent of the script's directory.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


@dataclass
class Axiom:
    name: str
    signature: str
    source_path: str       # relative to lean4/BEDC/
    line: int


@dataclass
class RegistryRow:
    name: str
    tier: str              # carrier | primitive | provisional
    signature: str
    role: str
    source_file: str
    replaces_when: str


VALID_TIERS = {"carrier", "primitive", "provisional"}


# ---------- source-tree axiom collection ----------

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
        # Compute line numbers
        for m in AXIOM_RE.finditer(text):
            name = m.group(1)
            sig = m.group(2).strip()
            qualified = f"{ns}.{name}" if ns else name
            line_no = text.count("\n", 0, m.start()) + 1
            rel = path.relative_to(repo_root / "lean4" / "BEDC").as_posix()
            out.append(Axiom(name=qualified, signature=sig, source_path=rel, line=line_no))
    return out


# ---------- registry parsing ----------

# Match a markdown table data row: starts with `|`, has at least 6 cells.
ROW_RE = re.compile(r"^\|\s*(BEDC\.[^\s|]+)\s*\|", re.MULTILINE)


def parse_registry(repo_root: Path) -> list[RegistryRow]:
    """Parse lean4/AXIOMS.md and return the data rows of the Registry table."""
    md_path = repo_root / "lean4" / "AXIOMS.md"
    if not md_path.exists():
        raise FileNotFoundError(f"AXIOMS.md not found at {md_path}")
    text = md_path.read_text(encoding="utf-8")

    rows: list[RegistryRow] = []
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        # Skip header separator
        if "---" in line:
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 6:
            continue
        name = cells[0]
        # Header rows: name == "name"; data rows: name starts with BEDC.
        if not name.startswith("BEDC."):
            continue
        rows.append(
            RegistryRow(
                name=name,
                tier=cells[1],
                signature=cells[2].strip("`"),
                role=cells[3],
                source_file=cells[4],
                replaces_when=cells[5],
            )
        )

    # Sanity: tiers must be valid
    for r in rows:
        if r.tier not in VALID_TIERS:
            raise ValueError(
                f"Registry row '{r.name}' has invalid tier '{r.tier}'; "
                f"must be one of {sorted(VALID_TIERS)}"
            )

    return rows


# ---------- audit ----------

@dataclass
class AuditResult:
    source_count: int
    registry_count: int
    unregistered: list[Axiom] = field(default_factory=list)
    missing_in_source: list[RegistryRow] = field(default_factory=list)
    signature_mismatches: list[tuple[str, str, str]] = field(default_factory=list)  # (name, src_sig, reg_sig)
    source_file_mismatches: list[tuple[str, str, str]] = field(default_factory=list)  # (name, src_path, reg_path)

    @property
    def passed(self) -> bool:
        return (
            not self.unregistered
            and not self.missing_in_source
            and not self.signature_mismatches
            and not self.source_file_mismatches
        )


def audit(source: Iterable[Axiom], registry: Iterable[RegistryRow]) -> AuditResult:
    source_list = list(source)
    registry_list = list(registry)
    src_by_name = {a.name: a for a in source_list}
    reg_by_name = {r.name: r for r in registry_list}

    result = AuditResult(source_count=len(source_list), registry_count=len(registry_list))

    # Unregistered: in source but not in registry
    for name, ax in src_by_name.items():
        if name not in reg_by_name:
            result.unregistered.append(ax)

    # Missing in source: in registry but not in source
    for name, row in reg_by_name.items():
        if name not in src_by_name:
            result.missing_in_source.append(row)

    # Signature mismatches (where both sides have the entry)
    for name in set(src_by_name) & set(reg_by_name):
        ax = src_by_name[name]
        row = reg_by_name[name]
        # Normalize whitespace
        src_norm = " ".join(ax.signature.split())
        reg_norm = " ".join(row.signature.split())
        if src_norm != reg_norm:
            result.signature_mismatches.append((name, src_norm, reg_norm))
        if ax.source_path != row.source_file:
            result.source_file_mismatches.append((name, ax.source_path, row.source_file))

    return result


# ---------- output ----------

def format_human(result: AuditResult) -> str:
    lines: list[str] = []
    lines.append(
        f"Axiom audit: {result.source_count} in source, "
        f"{result.registry_count} in registry"
    )
    if result.passed:
        lines.append("PASS: every source axiom is registered, every registered axiom is in source.")
        return "\n".join(lines)

    if result.unregistered:
        lines.append("")
        lines.append(f"FAIL: {len(result.unregistered)} unregistered axiom(s) in source:")
        for ax in result.unregistered:
            lines.append(f"  {ax.name}  ({ax.source_path}:{ax.line})  — :  {ax.signature}")
        lines.append("Action: add a row to lean4/AXIOMS.md, or remove the axiom from source.")

    if result.missing_in_source:
        lines.append("")
        lines.append(f"FAIL: {len(result.missing_in_source)} registered axiom(s) missing from source:")
        for row in result.missing_in_source:
            lines.append(f"  {row.name}  ({row.source_file})  [tier={row.tier}]")
        lines.append("Action: remove the row from lean4/AXIOMS.md, or restore the source axiom.")

    if result.signature_mismatches:
        lines.append("")
        lines.append(f"FAIL: {len(result.signature_mismatches)} signature mismatch(es):")
        for name, src, reg in result.signature_mismatches:
            lines.append(f"  {name}")
            lines.append(f"    source:   {src}")
            lines.append(f"    registry: {reg}")
        lines.append("Action: resync registry signature or source signature.")

    if result.source_file_mismatches:
        lines.append("")
        lines.append(f"FAIL: {len(result.source_file_mismatches)} source-file mismatch(es):")
        for name, src, reg in result.source_file_mismatches:
            lines.append(f"  {name}")
            lines.append(f"    source path:   {src}")
            lines.append(f"    registry path: {reg}")
        lines.append("Action: resync registry source_file column.")

    return "\n".join(lines)


def format_json(result: AuditResult) -> str:
    payload = {
        "passed": result.passed,
        "source_count": result.source_count,
        "registry_count": result.registry_count,
        "unregistered": [
            {"name": a.name, "signature": a.signature, "source_path": a.source_path, "line": a.line}
            for a in result.unregistered
        ],
        "missing_in_source": [
            {"name": r.name, "tier": r.tier, "source_file": r.source_file}
            for r in result.missing_in_source
        ],
        "signature_mismatches": [
            {"name": n, "source": s, "registry": r}
            for n, s, r in result.signature_mismatches
        ],
        "source_file_mismatches": [
            {"name": n, "source": s, "registry": r}
            for n, s, r in result.source_file_mismatches
        ],
    }
    return json.dumps(payload, indent=2)


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit BEDC axiom declarations against AXIOMS.md")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--json", action="store_true", help="emit JSON to stdout")
    args = parser.parse_args()

    try:
        source = collect_source_axioms(args.repo_root)
        registry = parse_registry(args.repo_root)
    except (FileNotFoundError, ValueError) as exc:
        print(f"setup error: {exc}", file=sys.stderr)
        return 2

    result = audit(source, registry)
    if args.json:
        print(format_json(result))
    else:
        print(format_human(result), file=sys.stderr if not result.passed else sys.stdout)
    return 0 if result.passed else 1


if __name__ == "__main__":
    sys.exit(main())
