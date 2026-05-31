#!/usr/bin/env python3
"""Glossary coverage survey with optional strict gate.

Four coverage checks run on every invocation:

  Check 1 -- region coverage:
      Every region id appearing as a node in the auto-derived
      ``docs/dossier/data/dependency.json`` must have a corresponding
      entry in the glossary. If a Lean module or paper chapter
      introduces a new region, the glossary must grow with it.

  Check 2 -- preamble coverage:
      Every project-concept ``\\newcommand`` declared in
      ``papers/bedc/preamble.tex`` must be reachable from the
      glossary, either directly by name or via the ``aliases`` field on
      a glossary entry. Macros listed in ``_meta.exempt_macros`` are
      skipped (rendering helpers, canonical aliases, internal carrier
      predicates etc.).

  Check 3 -- bilingual completeness:
      Every glossary entry must have a Chinese ``zh.label`` distinct
      from its English ``en.label``, except for entries explicitly
      listed in ``_meta.label_identical_ok`` (technical identifiers with
      no Chinese rendering).

  Check 4 -- constructive-story bilingual:
      Whenever a dependency-graph node carries a non-empty
      ``constructive_story_en`` (extracted from a paper closurestatus
      block), the corresponding glossary entry must supply a non-empty
      ``constructive_story_zh`` so the dossier ZH view does not silently
      fall back to English.

This script holds NO domain data of its own; everything it gates on
lives in ``docs/dossier/data_source/glossary/`` (one TOML file per
term plus ``_meta.toml``) and in the auto-derived dependency graph.
Edit the per-term TOML to add / fix entries.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _glossary_loader import GLOSSARY_DIR, load_glossary  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
DEP_DATA = ROOT / "docs" / "dossier" / "data" / "dependency.json"
PREAMBLE = ROOT / "papers" / "bedc" / "preamble.tex"


@dataclass
class GlossaryIssues:
    duplicate_aliases: list[str] = field(default_factory=list)
    missing_regions: list[str] = field(default_factory=list)
    missing_macros: list[str] = field(default_factory=list)
    bilingual_issues: list[str] = field(default_factory=list)
    missing_zh_stories: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    @property
    def total(self) -> int:
        return (
            len(self.duplicate_aliases)
            + len(self.missing_regions)
            + len(self.missing_macros)
            + len(self.bilingual_issues)
            + len(self.missing_zh_stories)
        )


def parse_preamble_macros(preamble: Path) -> set[str]:
    """Extract every ``\\newcommand{\\X}`` macro name from the preamble."""
    macros: set[str] = set()
    macro_re = re.compile(r"^\\newcommand\{\\([A-Za-z]+)")
    for line in preamble.read_text(encoding="utf-8").splitlines():
        m = macro_re.match(line)
        if m:
            macros.add(m.group(1))
    return macros


def build_alias_map(entries: dict[str, dict], issues: GlossaryIssues) -> dict[str, str]:
    alias_to_key: dict[str, str] = {}
    for key, entry in entries.items():
        for alias in entry.get("aliases", []):
            if alias in alias_to_key and alias_to_key[alias] != key:
                issues.duplicate_aliases.append(
                    f"duplicate alias '{alias}' on both '{alias_to_key[alias]}' and '{key}'"
                )
                continue
            alias_to_key[alias] = key
    return alias_to_key


def collect_issues(glossary: dict) -> tuple[GlossaryIssues, int, int, int]:
    issues = GlossaryIssues()
    meta = glossary.get("_meta", {})
    exempt_macros: set[str] = set(meta.get("exempt_macros", []))
    label_identical_ok: set[str] = set(meta.get("label_identical_ok", []))

    entries = {k: v for k, v in glossary.items() if not k.startswith("_")}
    glossary_keys = set(entries.keys())
    alias_to_key = build_alias_map(entries, issues)

    if DEP_DATA.exists():
        with DEP_DATA.open(encoding="utf-8") as fh:
            dep = json.load(fh)
        for node in dep.get("nodes", []):
            nid = node.get("id", "")
            if not nid:
                continue
            if nid not in glossary_keys and nid not in alias_to_key:
                issues.missing_regions.append(nid)
    else:
        issues.notes.append(
            f"[check-glossary] note: {DEP_DATA.relative_to(ROOT)} not built yet; "
            "skipping region-coverage check"
        )

    if PREAMBLE.exists():
        for m in sorted(parse_preamble_macros(PREAMBLE)):
            if m in exempt_macros:
                continue
            if m in glossary_keys:
                continue
            if m in alias_to_key:
                continue
            issues.missing_macros.append(m)
    else:
        issues.notes.append(f"[check-glossary] preamble not found: {PREAMBLE}")

    if DEP_DATA.exists():
        with DEP_DATA.open(encoding="utf-8") as fh:
            dep = json.load(fh)
        for node in dep.get("nodes", []):
            en = (node.get("constructive_story_en") or "").strip()
            if not en:
                continue
            nid = node.get("id", "")
            target = entries.get(nid)
            if target is None and nid in alias_to_key:
                target = entries.get(alias_to_key[nid])
            if target is None:
                continue
            zh = (target.get("constructive_story_zh") or "").strip()
            if not zh:
                issues.missing_zh_stories.append(nid)

    for key, entry in entries.items():
        en_label = entry.get("en", {}).get("label", "")
        zh_label = entry.get("zh", {}).get("label", "")
        if not en_label or not zh_label:
            issues.bilingual_issues.append(f"entry '{key}' missing en.label or zh.label")
            continue
        if en_label == zh_label and key not in label_identical_ok:
            issues.bilingual_issues.append(
                f"entry '{key}' has identical en/zh labels '{en_label}' "
                "(localise zh.label or add the key to _meta.label_identical_ok)"
            )

    return issues, len(entries), len(alias_to_key), len(exempt_macros)


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Survey glossary coverage, or fail on coverage gaps with --strict.",
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--survey",
        action="store_true",
        help="report coverage issues as advisory warnings and exit 0",
    )
    mode.add_argument(
        "--strict",
        action="store_true",
        help="fail with a nonzero exit code when coverage issues are present",
    )
    return parser.parse_args(argv)


def print_issue_list(title: str, values: list[str], *, slash_prefix: bool = False) -> None:
    if not values:
        return
    print(f"  {title} ({len(values)}):", file=sys.stderr)
    for value in sorted(values):
        prefix = "\\" if slash_prefix else ""
        print(f"    - {prefix}{value}", file=sys.stderr)


def report_issues(issues: GlossaryIssues, mode_name: str) -> int:
    for note in issues.notes:
        print(note, file=sys.stderr)

    if issues.total:
        if mode_name == "strict":
            print(f"[check-glossary] STRICT/FAIL: {issues.total} issues; exit nonzero", file=sys.stderr)
        else:
            print(
                f"[check-glossary] SURVEY/WARN: {issues.total} issues; exit 0 by design",
                file=sys.stderr,
            )
        print_issue_list("Duplicate aliases", issues.duplicate_aliases)
        print_issue_list("Missing region entries", issues.missing_regions)
        print_issue_list("Missing preamble macros", issues.missing_macros, slash_prefix=True)
        print_issue_list("Bilingual entry problems", issues.bilingual_issues)
        print_issue_list("Missing zh constructive stories", issues.missing_zh_stories)
        print(
            "\n[check-glossary] hint: edit docs/dossier/data_source/glossary/<key>.toml "
            "to add or fix entries, or update _meta.toml's exempt_macros / "
            "label_identical_ok if a term is intentionally not in scope.",
            file=sys.stderr,
        )
        return 1 if mode_name == "strict" else 0
    return 0


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    mode_name = "strict" if args.strict else "survey"

    if not GLOSSARY_DIR.is_dir():
        print(f"[check-glossary] glossary source dir missing: {GLOSSARY_DIR}", file=sys.stderr)
        return 1

    glossary = load_glossary()
    issues, entry_count, alias_count, exempt_macro_count = collect_issues(glossary)
    issue_exit = report_issues(issues, mode_name)
    if issues.total:
        return issue_exit

    print(
        f"[check-glossary] OK: {entry_count} entries cover all project concepts "
        f"({alias_count} aliases, {exempt_macro_count} exempt macros).",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
