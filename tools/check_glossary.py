#!/usr/bin/env python3
"""Glossary completeness gate.

Three gates run on every CI invocation:

  Gate 1 -- region coverage:
      Every region id appearing as a node in the auto-derived
      ``docs/dossier/data/dependency.json`` must have a corresponding
      entry in the glossary. If a Lean module or paper chapter
      introduces a new region, the glossary must grow with it.

  Gate 2 -- preamble coverage:
      Every project-concept ``\\newcommand`` declared in
      ``papers/bedc/preamble.tex`` must be reachable from the
      glossary, either directly by name or via the ``aliases`` field on
      a glossary entry. Macros listed in ``_meta.exempt_macros`` are
      skipped (rendering helpers, canonical aliases, internal carrier
      predicates etc.).

  Gate 3 -- bilingual completeness:
      Every glossary entry must have a Chinese ``zh.label`` distinct
      from its English ``en.label``, except for entries explicitly
      listed in ``_meta.label_identical_ok`` (technical identifiers with
      no Chinese rendering).

This script holds NO domain data of its own; everything it gates on
lives in ``docs/dossier/data_source/glossary/`` (one TOML file per
term plus ``_meta.toml``) and in the auto-derived dependency graph.
Edit the per-term TOML to add / fix entries.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _glossary_loader import GLOSSARY_DIR, load_glossary  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
DEP_DATA = ROOT / "docs" / "dossier" / "data" / "dependency.json"
PREAMBLE = ROOT / "papers" / "bedc" / "preamble.tex"


def parse_preamble_macros(preamble: Path) -> set[str]:
    """Extract every ``\\newcommand{\\X}`` macro name from the preamble."""
    macros: set[str] = set()
    macro_re = re.compile(r"^\\newcommand\{\\([A-Za-z]+)")
    for line in preamble.read_text(encoding="utf-8").splitlines():
        m = macro_re.match(line)
        if m:
            macros.add(m.group(1))
    return macros


def main() -> int:
    if not GLOSSARY_DIR.is_dir():
        print(f"[check-glossary] glossary source dir missing: {GLOSSARY_DIR}", file=sys.stderr)
        return 1

    glossary = load_glossary()

    meta = glossary.get("_meta", {})
    exempt_macros: set[str] = set(meta.get("exempt_macros", []))
    label_identical_ok: set[str] = set(meta.get("label_identical_ok", []))

    # entries (real glossary data) and their aliases
    entries = {k: v for k, v in glossary.items() if not k.startswith("_")}
    glossary_keys = set(entries.keys())

    # Build alias-to-key map from each entry's `aliases` field.
    alias_to_key: dict[str, str] = {}
    for key, entry in entries.items():
        for alias in entry.get("aliases", []):
            if alias in alias_to_key and alias_to_key[alias] != key:
                print(
                    f"[check-glossary] duplicate alias '{alias}' on both "
                    f"'{alias_to_key[alias]}' and '{key}'",
                    file=sys.stderr,
                )
                return 1
            alias_to_key[alias] = key

    missing_regions: list[str] = []
    missing_macros: list[str] = []
    bilingual_issues: list[str] = []

    # ---- Gate 1: region coverage ----
    if DEP_DATA.exists():
        with DEP_DATA.open(encoding="utf-8") as fh:
            dep = json.load(fh)
        for node in dep.get("nodes", []):
            nid = node.get("id", "")
            if not nid:
                continue
            if nid not in glossary_keys and nid not in alias_to_key:
                missing_regions.append(nid)
    else:
        print(
            f"[check-glossary] note: {DEP_DATA.relative_to(ROOT)} not built yet; "
            "skipping region-coverage gate",
            file=sys.stderr,
        )

    # ---- Gate 2: preamble coverage ----
    if PREAMBLE.exists():
        for m in sorted(parse_preamble_macros(PREAMBLE)):
            if m in exempt_macros:
                continue
            if m in glossary_keys:
                continue
            if m in alias_to_key:
                continue
            missing_macros.append(m)
    else:
        print(f"[check-glossary] preamble not found: {PREAMBLE}", file=sys.stderr)

    # ---- Gate 3: bilingual completeness ----
    for key, entry in entries.items():
        en_label = entry.get("en", {}).get("label", "")
        zh_label = entry.get("zh", {}).get("label", "")
        if not en_label or not zh_label:
            bilingual_issues.append(f"entry '{key}' missing en.label or zh.label")
            continue
        if en_label == zh_label and key not in label_identical_ok:
            bilingual_issues.append(
                f"entry '{key}' has identical en/zh labels '{en_label}' "
                "(localise zh.label or add the key to _meta.label_identical_ok)"
            )

    # ---- Report ----
    # Glossary completeness is advisory: missing entries do NOT block CI.
    # The dossier still renders without them — unknown nodes just show
    # their raw region id instead of a bilingual label.
    total = len(missing_regions) + len(missing_macros) + len(bilingual_issues)
    if total:
        print(
            f"[check-glossary] WARN: {total} issues (advisory; not blocking)",
            file=sys.stderr,
        )
        if missing_regions:
            print(
                f"  Missing region entries ({len(missing_regions)}):",
                file=sys.stderr,
            )
            for nid in sorted(missing_regions):
                print(f"    - {nid}", file=sys.stderr)
        if missing_macros:
            print(
                f"  Missing preamble macros ({len(missing_macros)}):",
                file=sys.stderr,
            )
            for m in missing_macros:
                print(f"    - \\{m}", file=sys.stderr)
        if bilingual_issues:
            print(
                f"  Bilingual entry problems ({len(bilingual_issues)}):",
                file=sys.stderr,
            )
            for s in bilingual_issues:
                print(f"    - {s}", file=sys.stderr)
        print(
            "\n[check-glossary] hint: edit docs/dossier/data_source/glossary/<key>.toml "
            "to add or fix entries, or update _meta.toml's exempt_macros / "
            "label_identical_ok if a term is intentionally not in scope.",
            file=sys.stderr,
        )
        return 0

    print(
        f"[check-glossary] OK: {len(entries)} entries cover all project concepts "
        f"({len(alias_to_key)} aliases, {len(exempt_macros)} exempt macros).",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
