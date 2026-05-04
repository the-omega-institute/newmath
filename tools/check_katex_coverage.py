#!/usr/bin/env python3
"""KaTeX coverage diagnostic for the BEDC dossier transit-map renderer.

Scans docs/dossier/data/theorem_graph.json against
docs/dossier/data_source/katex_glossary.json and reports how many
declarations' short names match a glossary entry. The remainder fall to
tier 3 (monospace) fallback in lean_to_katex.js at render time.

This script is **warn-only by design**. It always exits 0. KaTeX coverage
is a presentation-layer aesthetic for the dossier visualization — NOT a
soundness invariant of the Lean formalization. Compare with
tools/check-axioms.py, which is hard-fail because the 0-axiom invariant IS
load-bearing.

Wired into .github/workflows/dossier.yml as a non-failing diagnostic step
after build_theorem_graph.py — devs see coverage drift when new BEDC
theorems land that introduce kernel operator names not yet curated in
katex_glossary.json. The fix is to extend the glossary; the build never
fails on it.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_GRAPH = ROOT / "docs" / "dossier" / "data" / "theorem_graph.json"
DEFAULT_GLOSSARY = ROOT / "docs" / "dossier" / "data_source" / "katex_glossary.json"


def load_json(path: Path):
    with path.open(encoding="utf-8") as fh:
        return json.load(fh)


def short_name(qualified: str) -> str:
    """Last dot-separated segment, e.g. BEDC.FKernel.cont_assoc -> cont_assoc."""
    return qualified.rsplit(".", 1)[-1]


def coverage_stats(records: list[dict], glossary: dict) -> dict:
    """Count declarations whose short name OR fully qualified name matches a
    glossary key. Optimistic — error on the side of marking as covered."""
    glossary_keys = set(glossary.keys())
    total = len(records)
    covered = 0
    for r in records:
        name = r.get("name", "")
        if not name:
            continue
        if name in glossary_keys:
            covered += 1
            continue
        if short_name(name) in glossary_keys:
            covered += 1
            continue
    return {
        "total": total,
        "covered": covered,
        "fallback": total - covered,
        "pct": (covered / total * 100.0) if total else 0.0,
        "glossary_size": len(glossary),
    }


def report(stats: dict, *, file=sys.stderr) -> None:
    print(
        f"[check-katex-coverage] {stats['glossary_size']} entries in "
        f"katex_glossary.json",
        file=file,
    )
    print(
        f"[check-katex-coverage] {stats['covered']}/{stats['total']} "
        f"declaration short names match a glossary key "
        f"({stats['pct']:.1f}%)",
        file=file,
    )
    print(
        f"[check-katex-coverage] {stats['fallback']} declarations would "
        f"fall to tier 3 monospace fallback",
        file=file,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.strip().split("\n")[0])
    parser.add_argument("--graph", default=str(DEFAULT_GRAPH))
    parser.add_argument("--glossary", default=str(DEFAULT_GLOSSARY))
    args = parser.parse_args()

    graph_path = Path(args.graph)
    glossary_path = Path(args.glossary)

    if not graph_path.exists():
        print(
            f"[check-katex-coverage] WARNING: {graph_path} not found "
            f"(run build_theorem_graph.py first); skipping coverage diagnostic.",
            file=sys.stderr,
        )
        return 0
    if not glossary_path.exists():
        print(
            f"[check-katex-coverage] WARNING: {glossary_path} not found; "
            f"skipping coverage diagnostic.",
            file=sys.stderr,
        )
        return 0

    graph = load_json(graph_path)
    glossary = load_json(glossary_path)
    records = graph.get("theorems") or graph.get("records") or []

    stats = coverage_stats(records, glossary)
    report(stats)
    return 0


if __name__ == "__main__":
    sys.exit(main())
