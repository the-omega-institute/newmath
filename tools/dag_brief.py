#!/usr/bin/env python3
"""LLM-friendly compact view of the BEDC chapter DAG.

Reads BEDC raw sources directly (paper .tex closurestatus blocks +
\\autoref cross-chapter citations); does NOT depend on the dossier
visualisation pipeline. Always reflects the live state at the
moment of invocation.

For each chapter under `papers/bedc/parts/concrete_instances/`,
emits:

  - id / label                    (slug + region name from closurestatus)
  - theoryclosure / formalstatus  (current closure axes)
  - origin                        (human / ai)
  - depends_on[]                  (slugs of chapters cited via \\autoref)
  - thms                          (paper theorem/definition count
                                   inside the chapter file)

Output is a single JSON, ~50 KB, listing every chapter slug. A codex
round can `cat docs/dossier/data/dag_brief.json` once and reason
about the full DAG without burning prompt budget on
constructive-story paragraphs or cross-referencing multiple files.

Usage:
  python3 tools/dag_brief.py                              # stdout
  python3 tools/dag_brief.py --out <path>                 # write to file
  python3 tools/dag_brief.py --frontier                   # also list mature leaves
"""

from __future__ import annotations
import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PARTS_ROOT = REPO / "papers/bedc/parts"
CHAPTERS_DIR = PARTS_ROOT / "concrete_instances"

# A chapter file looks like `<NN>_<slug>_namecert_construction.tex`.
CHAPTER_FILENAME_RE = re.compile(
    r"^(\d+)_([a-z][a-z0-9_]*)_namecert_construction\.tex$"
)

# `\begin{closurestatus}{\<X>Up}` — captures region name without the Up.
CLOSURESTATUS_BEGIN_RE = re.compile(
    r"\\begin\{closurestatus\}\{\s*\\?([A-Za-z][A-Za-z0-9_]*)Up\s*\}"
)

# Field-line regex (mirrors bedc_ci.py for self-containment).
CLOSURESTATUS_FIELD_RE = re.compile(
    r"\\(theoryclosure|formalstatus|origin|bridgestatus)\{([^}]*)\}"
)

# Cross-chapter citation: `\autoref{ch:concrete-instances-<slug>-namecert}`.
AUTOREF_RE = re.compile(
    r"\\autoref\{ch:concrete-instances-([a-z][a-z0-9_-]*)-namecert\}"
)

# Theorem / definition / lemma counter inside a chapter file.
THM_RE = re.compile(
    r"\\begin\{(theorem|definition|lemma|corollary|proposition)\}"
)


def parse_chapter(path: Path) -> dict | None:
    m = CHAPTER_FILENAME_RE.match(path.name)
    if not m:
        return None
    slug = m.group(2)
    text = path.read_text(errors="replace")
    region = None
    fields: dict[str, str] = {}
    bm = CLOSURESTATUS_BEGIN_RE.search(text)
    if bm:
        region = bm.group(1)
        # Walk forward until \end{closurestatus} to collect fields.
        end_idx = text.find("\\end{closurestatus}", bm.end())
        body = text[bm.end():end_idx] if end_idx != -1 else text[bm.end():]
        for fm in CLOSURESTATUS_FIELD_RE.finditer(body):
            fields[fm.group(1)] = fm.group(2).strip().lstrip("\\")
    deps: set[str] = set()
    for am in AUTOREF_RE.finditer(text):
        dep = am.group(1).replace("-", "_")
        if dep != slug:
            deps.add(dep)
    thms = len(THM_RE.findall(text))
    return {
        "id": slug,
        "label": region or slug,
        "theoryclosure": fields.get("theoryclosure") or None,
        "formalstatus": fields.get("formalstatus") or None,
        "origin": (fields.get("origin") or "human").lower(),
        "thms": thms,
        "depends_on": sorted(deps),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=str, default=None)
    parser.add_argument("--frontier", action="store_true")
    args = parser.parse_args()

    if not CHAPTERS_DIR.exists():
        print(f"missing {CHAPTERS_DIR}", file=sys.stderr)
        return 1

    nodes: list[dict] = []
    for f in sorted(CHAPTERS_DIR.glob("*_namecert_construction.tex")):
        info = parse_chapter(f)
        if info:
            nodes.append(info)

    # Compute downstream count: how many other chapters depend on me.
    downstream = defaultdict(int)
    for n in nodes:
        for d in n["depends_on"]:
            downstream[d] += 1
    for n in nodes:
        n["downstream"] = downstream.get(n["id"], 0)

    out: dict = {
        "node_count": len(nodes),
        "edge_count": sum(len(n["depends_on"]) for n in nodes),
        "nodes": nodes,
    }

    if args.frontier:
        mature_grades = {"publicClosure", "bridgedClosure", "matureClosure"}
        frontier = [
            n for n in nodes
            if n.get("theoryclosure") in mature_grades and n.get("downstream", 0) <= 1
        ]
        frontier.sort(key=lambda x: -x.get("thms", 0))
        out["frontier_chapters"] = [
            {"id": n["id"], "label": n["label"], "thms": n["thms"],
             "grade": n["theoryclosure"]}
            for n in frontier[:40]
        ]

    text = json.dumps(out, indent=2, ensure_ascii=False)
    if args.out:
        outp = Path(args.out)
        outp.parent.mkdir(parents=True, exist_ok=True)
        outp.write_text(text + "\n")
        try:
            disp = outp.relative_to(REPO)
        except ValueError:
            disp = outp
        print(f"[dag_brief] wrote {disp} -- "
              f"{len(nodes)} nodes, "
              f"{out['edge_count']} edges, {len(text)//1024} KB",
              file=sys.stderr)
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
