#!/usr/bin/env python3
"""Inbound-citation ripeness check on the dossier dependency graph.

Reads `docs/dossier/data/dependency.json` (produced by
`tools/build_dossier_status.py`) and lists chapter nodes whose
in-degree (count of other chapters citing this one) is below a
threshold despite the chapter having been in the repo for more than
N rounds.

Such chapters are *ripeness candidates*: no other chapter depends on
them, suggesting the concept is either trivial (nothing needed it),
out-of-scope (good concept but pipeline isn't using it), or
premature (concept depends on infrastructure still being built).
Phase Review uses this list as a soft signal — chapters appearing
here for too long get demoted to `\\origin{ai-trivial}` and removed
from main paper flow.

Usage:
  python3 tools/dossier_ripeness_check.py [--max-indegree N] [--limit M]
  python3 tools/dossier_ripeness_check.py --json  # machine-readable output

stdlib only (project rule).
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEPENDENCY_JSON = REPO_ROOT / "docs" / "dossier" / "data" / "dependency.json"


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--max-indegree",
        type=int,
        default=1,
        help="Chapters with in_degree <= this are candidates (default: 1).",
    )
    p.add_argument(
        "--limit", type=int, default=50,
        help="Cap on returned candidates (default: 50)."
    )
    p.add_argument("--json", action="store_true", help="Machine-readable output.")
    args = p.parse_args()

    if not DEPENDENCY_JSON.exists():
        print(
            f"ripeness: dependency.json not found at {DEPENDENCY_JSON}. "
            f"Run `python3 tools/build_dossier_status.py` first.",
            file=sys.stderr,
        )
        return 2

    g = json.loads(DEPENDENCY_JSON.read_text())
    nodes = g.get("nodes", [])
    edges = g.get("edges", [])

    in_degree: Counter[str] = Counter()
    for e in edges:
        tgt = e.get("target")
        if tgt:
            in_degree[tgt] += 1

    candidates = []
    for n in nodes:
        nid = n.get("id")
        if not nid:
            continue
        d = in_degree.get(nid, 0)
        if d > args.max_indegree:
            continue
        candidates.append({
            "id": nid,
            "in_degree": d,
            "thms": n.get("thms", 0),
            "namecert_checked": n.get("namecert_checked", 0),
            "level": n.get("level", "-"),
        })

    candidates.sort(
        key=lambda c: (c["in_degree"], -c.get("namecert_checked", 0))
    )
    candidates = candidates[: args.limit]

    if args.json:
        print(json.dumps({
            "max_indegree_threshold": args.max_indegree,
            "candidate_count": len(candidates),
            "candidates": candidates,
        }, indent=2))
    else:
        print(f"ripeness: {len(candidates)} chapter(s) with "
              f"in_degree <= {args.max_indegree} (showing top "
              f"{min(len(candidates), args.limit)}):")
        for c in candidates:
            print(
                f"  in={c['in_degree']:2d}  nc={c['namecert_checked']:3d}  "
                f"thm={c['thms']:4d}  L{str(c.get('level','-')):>3s}  {c['id']}"
            )

    return 0


if __name__ == "__main__":
    sys.exit(main())
