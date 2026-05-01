#!/usr/bin/env python3
"""Critical-path discovery for BEDC derived horizon coverage.

Picks the next domains Phase B should attack: high downstream impact, low
current implementation, dependencies already implemented. Used as a HARD
GATE in `lean4/scripts/prompts/phase_b.txt` so codex stops re-saturating
the same five domains and starts opening new fronts.

Run with no arguments. Output is JSON to stdout.
"""

from __future__ import annotations

import json
import re
from collections import deque
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NAMECERT_GLOB = ROOT / "papers/bedc/parts/concrete_instances"
DERIVED_DIR = ROOT / "lean4/BEDC/Derived"

# Lower bound for "node is implemented enough that its dependents may proceed".
DEPS_READY_THRESHOLD = 5
# Upper bound for "node is saturated; do not pick further".
SATURATION_THRESHOLD = 20

NAME_RE = re.compile(r"^\d+_([a-z][a-z0-9]*)_namecert_construction\.tex$")
UP_REF_RE = re.compile(r"\\?([A-Z][A-Za-z]*)Up\b")
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef)\{")


def normalize_name(stem: str) -> str:
    """Map paper file basename to canonical horizon key (lowercase)."""
    m = NAME_RE.match(stem)
    return m.group(1) if m else stem.lower()


def extract_horizons() -> dict[str, dict]:
    """Scan namecert chapters; return {name: {file_paper, deps, thms}}."""
    horizons: dict[str, dict] = {}
    for tex in sorted(NAMECERT_GLOB.glob("*_namecert_construction.tex")):
        name = normalize_name(tex.name)
        text = tex.read_text(encoding="utf-8", errors="replace")
        deps = {m.group(1).lower() for m in UP_REF_RE.finditer(text)}
        deps.discard(name)
        thms = len(LEAN_MARKER_RE.findall(text))
        lean_file = DERIVED_DIR / (
            "".join(p.capitalize() for p in name.split("_")) + "Up.lean"
        )
        horizons[name] = {
            "name": name,
            "deps": sorted(deps),
            "thms": thms,
            "file_paper": str(tex.relative_to(ROOT)),
            "file_lean": str(lean_file.relative_to(ROOT)),
        }
    return horizons


def transitive_downstream(horizons: dict[str, dict]) -> dict[str, int]:
    """For each node N, count how many distinct horizons transitively
    depend on N (BFS over the inverted dep graph)."""
    down: dict[str, set[str]] = {n: set() for n in horizons}
    for n, info in horizons.items():
        for d in info["deps"]:
            if d in down:
                down[d].add(n)
    out: dict[str, int] = {}
    for n in horizons:
        seen: set[str] = set()
        q: deque[str] = deque(down[n])
        while q:
            x = q.popleft()
            if x in seen:
                continue
            seen.add(x)
            q.extend(down.get(x, set()) - seen)
        out[n] = len(seen)
    return out


def deps_ready(name: str, horizons: dict[str, dict]) -> bool:
    """All declared deps must already have >= DEPS_READY_THRESHOLD theorems."""
    for d in horizons[name]["deps"]:
        if d not in horizons:
            continue  # external (e.g. a kernel object); ignore
        if horizons[d]["thms"] < DEPS_READY_THRESHOLD:
            return False
    return True


def main() -> int:
    horizons = extract_horizons()
    downstream = transitive_downstream(horizons)
    ranked: list[dict] = []
    for n, info in horizons.items():
        if info["thms"] >= SATURATION_THRESHOLD:
            continue
        if not deps_ready(n, horizons):
            continue
        score = downstream[n] / (1.0 + info["thms"])
        ranked.append({
            **info,
            "downstream": downstream[n],
            "score": round(score, 2),
        })
    ranked.sort(key=lambda r: (-r["score"], -r["downstream"], r["name"]))
    payload = {
        "computed_at": datetime.now(timezone.utc).isoformat(),
        "deps_ready_threshold": DEPS_READY_THRESHOLD,
        "saturation_threshold": SATURATION_THRESHOLD,
        "top": ranked[:10],
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
