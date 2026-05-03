#!/usr/bin/env python3
"""Critical-path discovery for BEDC derived horizon coverage.

Picks the next domains Phase B should attack: high downstream impact, low
current implementation, dependencies already implemented. Used as a HARD
GATE in `lean4/scripts/prompts/phase_b.txt` so codex stops re-saturating
the same five domains and starts opening new fronts.

Run with no arguments. Output is JSON to stdout.
"""

from __future__ import annotations

import fcntl
import json
import os
import re
import time
from collections import deque
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NAMECERT_GLOB = ROOT / "papers/bedc/parts/concrete_instances"
DERIVED_DIR = ROOT / "lean4/BEDC/Derived"

# Per-call rolling cooldown: when 8+ paper reviewers run critical_path in the
# same minute they all see identical scores and converge on the same top-1,
# producing a dedup pile-up downstream. Each invocation atomically picks the
# best non-locked node and writes it to LOCKS_FILE so the next concurrent
# invocation skips it. Locks expire after LOCK_TTL_SECONDS so when a round
# finishes (or stalls) the anchor naturally re-enters the candidate pool.
LOCKS_FILE = ROOT / ".critical_path_locks.json"
LOCK_TTL_SECONDS = 1500  # 25 min — matches typical paper round duration

# Lower bound for "node is implemented enough that its dependents may proceed".
DEPS_READY_THRESHOLD = 5
# Upper bound for "node is saturated; do not pick further". Tightened from
# the original 20 to 10 because nat/int/ring at 12-15 thm were still in
# `top` even though further per-domain instances were pure parameter-echo
# bloat.
SATURATION_THRESHOLD = 10

# Horizons whose paper schemas are parametric (the chapter writes laws as
# `mul / add / neg : BHist -> BHist -> BHist` without specifying a
# concrete BHist function). Lean rounds picking these targets can only
# produce `(name : forall x y z, hsame ...)` parameter-echo schema —
# Phase D mechanically rejects exactly that shape, so the round is
# guaranteed to fail. Keep them out of `top` until the paper side adds a
# concrete `mul := λ h k => ...` definition.
SCHEMA_ONLY_HORIZONS: set[str] = {
    # abgroup / group / monoid / ring / commring / field / module / vecspace /
    # linearmap / matrix / polynomial / fps / lattice were originally banned
    # because their paper schema wrote laws as parametric operators. Paper
    # rounds P699-P811 (prompt v2.1 schema-only unlock HARD GATE) added
    # concrete singleton-history instances (Carrier := UnaryHistory, mul :=
    # Cont, e := BHist.Empty, smul := emp, etc.) that pin every abstract symbol
    # to a specific BHist function. Lean rounds can now produce BHist-anchored
    # proofs about these concrete instances rather than parameter-echo schema,
    # so they are out of the ban list. The remaining 3 order-theoretic
    # chapters still need the same paper-side unlock — they currently lack the
    # concrete singleton pinning of meet/join/le on a specific BHist value.
    "totalorder", "preorder", "poset",
}

NAME_RE = re.compile(r"^\d+_([a-z][a-z0-9]*)_namecert_construction\.tex$")
UP_REF_RE = re.compile(r"\\?([A-Z][A-Za-z]*)Up\b")
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef)\{")


def normalize_name(stem: str) -> str:
    """Map paper file basename to canonical horizon key (lowercase)."""
    m = NAME_RE.match(stem)
    return m.group(1) if m else stem.lower()


def derive_lean_camel_case(paper_key: str, paper_text: str) -> str:
    """Recover the canonical CamelCase form of a horizon name.

    `paper_key` is the lowercase basename (e.g. "abgroup", "commring",
    "linearmap"). The naive .capitalize() pass yields "Abgroup",
    "Commring", "Linearmap" — wrong for the multi-word horizons. The
    paper text always references the horizon as `\<X>Up`; we grep that
    and take the first match whose lowercase form equals `paper_key`.
    Falls back to `.capitalize()` only if no `<X>Up` reference exists
    (which shouldn't happen for any chapter that has been written).
    """
    for m in UP_REF_RE.finditer(paper_text):
        candidate = m.group(1)
        if candidate.lower() == paper_key:
            return candidate
    # Underscored split fallback (kept for paper basenames like `nat_trans`):
    return "".join(p.capitalize() for p in paper_key.split("_"))


def extract_horizons() -> dict[str, dict]:
    """Scan namecert chapters; return {name: {file_paper, deps, thms}}."""
    horizons: dict[str, dict] = {}
    for tex in sorted(NAMECERT_GLOB.glob("*_namecert_construction.tex")):
        name = normalize_name(tex.name)
        text = tex.read_text(encoding="utf-8", errors="replace")
        deps = {m.group(1).lower() for m in UP_REF_RE.finditer(text)}
        deps.discard(name)
        thms = len(LEAN_MARKER_RE.findall(text))
        camel = derive_lean_camel_case(name, text)
        lean_file = DERIVED_DIR / f"{camel}Up.lean"
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


def _claim_top_with_cooldown(ranked: list[dict]) -> list[dict]:
    """Atomically pick the best non-locked node, record it in LOCKS_FILE, and
    return a re-ordered top with locked nodes demoted to the bottom.

    Concurrent critical_path invocations serialize on flock so each one sees
    the latest lock state — 8 simultaneous reviewers will each pick a
    different top because each adds its choice to the lock file before the
    next gets the lock.
    """
    # Open with O_CREAT so we can flock even if the file doesn't exist yet.
    fd = os.open(LOCKS_FILE, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        try:
            os.lseek(fd, 0, 0)
            raw = os.read(fd, 1 << 20).decode("utf-8") or "{}"
            locks: dict[str, float] = json.loads(raw)
        except Exception:
            locks = {}
        now = time.time()
        # Drop expired locks
        locks = {k: v for k, v in locks.items() if v > now}
        locked_names = set(locks.keys())
        # Partition ranked into available / locked, preserve internal order
        available = [r for r in ranked if r["name"] not in locked_names]
        locked = [r for r in ranked if r["name"] in locked_names]
        # Claim the new top-1 (the available[0]) for this caller
        if available:
            locks[available[0]["name"]] = now + LOCK_TTL_SECONDS
        try:
            os.lseek(fd, 0, 0)
            os.ftruncate(fd, 0)
            os.write(fd, json.dumps(locks).encode("utf-8"))
        except Exception:
            pass
        return available + locked
    finally:
        try:
            fcntl.flock(fd, fcntl.LOCK_UN)
        except Exception:
            pass
        os.close(fd)


def main() -> int:
    horizons = extract_horizons()
    downstream = transitive_downstream(horizons)
    ranked: list[dict] = []
    for n, info in horizons.items():
        if n in SCHEMA_ONLY_HORIZONS:
            continue
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
    rolled = _claim_top_with_cooldown(ranked)
    payload = {
        "computed_at": datetime.now(timezone.utc).isoformat(),
        "deps_ready_threshold": DEPS_READY_THRESHOLD,
        "saturation_threshold": SATURATION_THRESHOLD,
        "top": rolled[:10],
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
