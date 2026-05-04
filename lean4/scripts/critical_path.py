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
import subprocess
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
#
# IMPORTANT: codex Phase B runs this script from inside per-round git
# worktrees (cwd=.worktrees/round_R<N>/...), so a path like
# `Path(__file__).parent / ".critical_path_locks.json"` resolves to a
# DIFFERENT file in each worktree's checkout — every concurrent worker
# would write its own lock that no sibling can see, defeating the cooldown.
# Anchor the file in the shared `.git` common dir instead: linked worktrees
# all share the main repo's `.git/` (returned by `git rev-parse
# --git-common-dir`), so one lock file is visible to every worker.
def _resolve_locks_file() -> Path:
    fallback = Path(__file__).resolve().parent / ".critical_path_locks.json"
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--git-common-dir"],
            cwd=str(Path(__file__).resolve().parent),
            capture_output=True,
            text=True,
            check=True,
            timeout=5,
        ).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
        return fallback
    if not out:
        return fallback
    common = Path(out)
    if not common.is_absolute():
        common = (Path(__file__).resolve().parent / common).resolve()
    return common / "bedc-critical-path-locks.json"


LOCKS_FILE = _resolve_locks_file()
LOCK_TTL_SECONDS = 1500  # 25 min — matches typical paper round duration

# Lower bound for "node is implemented enough that its dependents may proceed".
# Lives in `.pipeline_parallel.json` under key `deps_ready_threshold` so it
# can be tuned without restarting the orchestrator. Default 5; main() reads
# this once per call. main() also auto-relaxes (5→3→2→1) when the strict
# value yields `top=[]` so a momentarily-thin tree doesn't wedge the
# pipeline. Earlier wedge incident: 2026-05-04 08:00–09:30, 22 cooldowns
# burned because `field` was deps_ready=False with `commring=4 < 5`.
DEFAULT_DEPS_READY_THRESHOLD = 5
PARALLEL_CONFIG_FILE = ROOT / ".pipeline_parallel.json"


def read_deps_ready_threshold(default: int = DEFAULT_DEPS_READY_THRESHOLD) -> int:
    try:
        if PARALLEL_CONFIG_FILE.exists():
            data = json.loads(PARALLEL_CONFIG_FILE.read_text(encoding="utf-8"))
            v = int(data.get("deps_ready_threshold", default))
            return max(1, min(v, 20))
    except Exception:
        pass
    return default


# Legacy module-level constant kept for any importer that still references
# `cp.DEPS_READY_THRESHOLD`. main() now reads from the config file.
DEPS_READY_THRESHOLD = DEFAULT_DEPS_READY_THRESHOLD

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

NAME_RE = re.compile(r"^\d+_([a-z][a-z0-9_]*?)_namecert_construction\.tex$")
UP_REF_RE = re.compile(r"\\?([A-Z][A-Za-z]*)Up\b")
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef)\{")
# `\closureat{<X>Up}{<strength>}` is the per-chapter binary closure marker
# (preamble.tex). The chapter is "closed" iff a closureat with strength
# `\checkedCertStr` or `\bridgeCertStr` is present anywhere under the
# chapter's recursive include closure. Critical_path excludes closed
# chapters from `top` so codex rounds focus on still-open horizons.
CLOSUREAT_RE = re.compile(
    r"\\closureat\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}\{\s*\\(\w+)Str\s*\}"
)
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")
CLOSED_STRENGTHS = {"checkedCert", "bridgeCert"}
PAPER_ROOT_DIR = ROOT / "papers" / "bedc"


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


def _read_chapter_recursive(chapter_path: Path,
                              seen: "set | None" = None) -> str:
    """Read a paper chapter and recursively follow `\\input{...}` includes.
    Returns the concatenated text. `seen` guards against include cycles.
    All `\\input` paths are resolved relative to PAPER_ROOT_DIR (matching
    pdflatex's working directory)."""
    if seen is None:
        seen = set()
    chapter_path = chapter_path.resolve()
    if chapter_path in seen or not chapter_path.exists():
        return ""
    seen.add(chapter_path)
    try:
        text = chapter_path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return ""
    parts = [text]
    for m in INPUT_RE.finditer(text):
        rel = m.group(1).strip()
        if not rel.endswith(".tex"):
            rel = rel + ".tex"
        child = (PAPER_ROOT_DIR / rel).resolve()
        parts.append(_read_chapter_recursive(child, seen))
    return "".join(parts)


def is_chapter_closed(chapter_text: str, name: str) -> "str | None":
    """If chapter has `\\closureat{<Name>Up}{\\<strength>Str}` with strength
    in CLOSED_STRENGTHS, return the strength string. Else None."""
    target_lower = name.lower()
    for m in CLOSUREAT_RE.finditer(chapter_text):
        if m.group(1).lower() != target_lower:
            continue
        strength = m.group(2)  # e.g. "checkedCert" / "bridgeCert"
        if strength in CLOSED_STRENGTHS:
            return strength
    return None


def extract_horizons() -> dict[str, dict]:
    """Scan namecert chapters; return {name: {file_paper, deps, thms, closed_at}}."""
    horizons: dict[str, dict] = {}
    for tex in sorted(NAMECERT_GLOB.glob("*_namecert_construction.tex")):
        name = normalize_name(tex.name)
        text = tex.read_text(encoding="utf-8", errors="replace")
        # Resolve all included subfiles for closure / dep / marker scanning.
        full_text = _read_chapter_recursive(tex)
        deps = {m.group(1).lower() for m in UP_REF_RE.finditer(full_text)}
        deps.discard(name)
        thms = len(LEAN_MARKER_RE.findall(full_text))
        closed_at = is_chapter_closed(full_text, name)
        camel = derive_lean_camel_case(name, text)
        lean_file = DERIVED_DIR / f"{camel}Up.lean"
        horizons[name] = {
            "name": name,
            "deps": sorted(deps),
            "thms": thms,
            "closed_at": closed_at,           # None | "checkedCert" | "bridgeCert"
            "closed": closed_at is not None,
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


def deps_ready(name: str, horizons: dict[str, dict],
                threshold: int = DEFAULT_DEPS_READY_THRESHOLD) -> bool:
    """All declared deps must already have >= threshold theorems."""
    for d in horizons[name]["deps"]:
        if d not in horizons:
            continue  # external (e.g. a kernel object); ignore
        if horizons[d]["thms"] < threshold:
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


def _rank_at_threshold(horizons: dict[str, dict], downstream: dict[str, int],
                        threshold: int) -> list[dict]:
    """Rank OPEN horizons by transitive downstream impact.

    A horizon is "closed" iff its chapter has `\\closureat{<X>Up}{checkedCert
    or bridgeCert}` somewhere in its include closure — see preamble.tex
    `\\closureat` macro and `is_chapter_closed`. Closed horizons are
    excluded entirely (the binary closure replaces the old
    `thms >= SATURATION_THRESHOLD` heuristic).

    Among open horizons, score is `downstream` (binary). The legacy
    `score / (1 + thms)` denominator is preserved as a tiebreaker so that
    among horizons with equal downstream impact, the one with fewer
    `\\leanchecked` markers comes first (closer to a meaningful
    closureat opportunity).
    """
    ranked: list[dict] = []
    for n, info in horizons.items():
        if n in SCHEMA_ONLY_HORIZONS:
            continue
        if info.get("closed"):
            continue
        if not deps_ready(n, horizons, threshold):
            continue
        score = downstream[n]
        # Tiebreaker: prefer horizons with fewer thms (closer to a fresh
        # closureat opportunity, fewer accumulated wrappers).
        tiebreak = downstream[n] / (1.0 + info["thms"])
        ranked.append({
            **info,
            "downstream": downstream[n],
            "score": score,
            "tiebreak": round(tiebreak, 2),
        })
    ranked.sort(key=lambda r: (-r["score"], -r["tiebreak"], r["name"]))
    return ranked


def main() -> int:
    horizons = extract_horizons()
    downstream = transitive_downstream(horizons)

    # Read the strict threshold from .pipeline_parallel.json (default 5).
    strict = read_deps_ready_threshold()

    # Adaptive: try strict first; if empty, drop the threshold by 1 each
    # iteration down to 1. Avoids the "wedged at empty top" failure mode
    # where every pending horizon needs deps_ready=False because its single
    # dep is just shy of the cap (e.g. field needed commring=5 but had 4).
    relaxed_at = None
    ranked: list[dict] = []
    for t in range(strict, 0, -1):
        ranked = _rank_at_threshold(horizons, downstream, t)
        if ranked:
            if t < strict:
                relaxed_at = t
            break

    rolled = _claim_top_with_cooldown(ranked)

    # Closure stats: how many of each strength under the binary closure
    # marker `\closureat`. Useful for the daily self-check to track
    # progress toward full theory closure.
    closed_count = {"checkedCert": 0, "bridgeCert": 0}
    open_count = 0
    for info in horizons.values():
        c = info.get("closed_at")
        if c in closed_count:
            closed_count[c] += 1
        elif not info.get("closed"):
            open_count += 1

    payload = {
        "computed_at": datetime.now(timezone.utc).isoformat(),
        "deps_ready_threshold": strict,
        "deps_ready_threshold_used": relaxed_at if relaxed_at is not None else strict,
        "deps_ready_relaxed": relaxed_at is not None,
        "closed_horizons": closed_count,
        "open_horizons": open_count,
        "top": rolled[:10],
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
