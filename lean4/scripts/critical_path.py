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


def _resolve_paper_label_claims_file() -> Path:
    """Anchor matches `claim_paper_label.py`'s state file location."""
    fallback = Path(__file__).resolve().parent / ".paper_label_claims.json"
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--git-common-dir"],
            cwd=str(Path(__file__).resolve().parent),
            capture_output=True, text=True, check=True, timeout=5,
        ).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
        return fallback
    if not out:
        return fallback
    common = Path(out)
    if not common.is_absolute():
        common = (Path(__file__).resolve().parent / common).resolve()
    return common / "bedc-paper-label-claims.json"


PAPER_LABEL_CLAIMS_FILE = _resolve_paper_label_claims_file()


def _read_active_claimed_labels() -> set[str]:
    """Set of paper labels currently held by some in-flight round (TTL-fresh).

    Read from `claim_paper_label.py`'s shared JSON. Used by
    _rank_at_threshold to deduct claimed labels from per-sibling
    `unmarked` count — codex shouldn't pick a sibling whose available
    targets are already taken. Silent on errors (degrade to empty)."""
    try:
        if not PAPER_LABEL_CLAIMS_FILE.exists():
            return set()
        data = json.loads(PAPER_LABEL_CLAIMS_FILE.read_text(encoding="utf-8"))
        now = time.time()
        return {
            k for k, v in data.items()
            if isinstance(v, dict) and float(v.get("expires_at", 0)) > now
        }
    except Exception:
        return set()

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
PAPER_LABEL_RE = re.compile(r"\\label\{(thm|def|lem|prop|cor):")
PAPER_LABEL_FULL_RE = re.compile(r"\\label\{(thm|def|lem|prop|cor):([^}]+)\}")
# `\closureat{<X>Up}{<strength>}` is the per-chapter binary closure marker
# (preamble.tex). The chapter is "closed" iff a closureat with strength
# `\checkedCertStr` or `\bridgeCertStr` is present anywhere under the
# chapter's recursive include closure. Critical_path excludes closed
# chapters from `top` so codex rounds focus on still-open horizons.
CLOSUREAT_RE = re.compile(
    r"\\closureat\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}\{\s*\\(\w+)Str\s*\}"
    r"(?:\[\s*([^\]]+?)\s*\])?"
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
        strength = m.group(2)
        if strength in CLOSED_STRENGTHS:
            return strength
    return None


def chapter_closure_grounding(chapter_text: str, name: str) -> "str | None":
    """If chapter declares `\\closureat{<Name>Up}{...}[<lean.target>]`, return
    the grounding theorem with `\\_` resolved to `_`. Else None."""
    target_lower = name.lower()
    for m in CLOSUREAT_RE.finditer(chapter_text):
        if m.group(1).lower() != target_lower:
            continue
        grounding = m.group(3)
        if grounding:
            return grounding.replace("\\_", "_").strip()
    return None


def extract_horizons() -> dict[str, dict]:
    """Scan namecert chapters; return {name: {file_paper, deps, thms, closed_at, siblings}}.

    Each chapter's `siblings` is a list of dicts giving the sub-fronts a
    Lean round can attack independently. With the hub-only convention
    (CLAUDE.md / AGENTS.md), most modern chapters have many `\\input{...}`
    sibling files under `parts/concrete_instances/<theme>/`. Each sibling
    becomes its own front so concurrent workers can claim different sibling
    files of the same chapter without colliding.
    """
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
        grounding = chapter_closure_grounding(full_text, name)
        camel = derive_lean_camel_case(name, text)
        lean_file = DERIVED_DIR / f"{camel}Up.lean"
        siblings = _collect_siblings(tex, name, camel, lean_file)
        horizons[name] = {
            "name": name,
            "deps": sorted(deps),
            "thms": thms,
            "closed_at": closed_at,           # None | "checkedCert" | "bridgeCert"
            "closed": closed_at is not None,
            "closure_grounding": grounding,   # None | "BEDC.<...>"
            "file_paper": str(tex.relative_to(ROOT)),
            "file_lean": str(lean_file.relative_to(ROOT)),
            "siblings": siblings,
        }
    return horizons


def _collect_siblings(parent_tex: Path, chapter_name: str, camel: str,
                        lean_file: Path) -> list[dict]:
    """Enumerate per-sibling fronts within a chapter.

    A "sibling" is a unit of paper content a Lean round can claim
    independently. Resolution rule:

    * If the parent chapter has any `\\input{...}` directives (hub-only
      convention), each unique resolved input file is a sibling.
    * If parent inline body contains `\\begin\\{(theorem|definition|...)\\}`
      (legacy non-hub chapter), the parent file itself is also a sibling.
    * If neither (rare: empty stub chapter), the parent file is the sole
      sibling — keeps the chapter visible to the lock pool.

    Each sibling carries its own `file_paper` and `thms` counts so the
    ranker can prefer thinner siblings (closer to a fresh closure).
    """
    try:
        parent_text = parent_tex.read_text(encoding="utf-8", errors="replace")
    except Exception:
        parent_text = ""
    inputs = []
    for m in INPUT_RE.finditer(parent_text):
        rel = m.group(1).strip()
        if not rel.endswith(".tex"):
            rel = rel + ".tex"
        sib_path = (PAPER_ROOT_DIR / rel).resolve()
        if sib_path == parent_tex.resolve():
            continue
        inputs.append(sib_path)
    # Parent has inline content if it carries any theorem/definition env.
    inline_re = re.compile(
        r"\\begin\{(theorem|lemma|definition|proposition|corollary|example)\}"
    )
    parent_has_inline = bool(inline_re.search(parent_text))

    siblings: list[dict] = []
    seen: set[Path] = set()
    file_lean_str = str(lean_file.relative_to(ROOT))
    if inputs:
        for sib in inputs:
            if sib in seen or not sib.exists():
                continue
            seen.add(sib)
            try:
                sib_text = _read_chapter_recursive(sib)
            except Exception:
                sib_text = ""
            sib_thms = len(LEAN_MARKER_RE.findall(sib_text))
            sib_label_set = {f"{m.group(1)}:{m.group(2)}"
                              for m in PAPER_LABEL_FULL_RE.finditer(sib_text)}
            sib_labels = len(sib_label_set)
            sib_unmarked = max(0, sib_labels - sib_thms)
            sib_closed = is_chapter_closed(sib_text, chapter_name) is not None
            siblings.append({
                "name": chapter_name,
                "sibling_id": sib.stem,
                "file_paper": str(sib.relative_to(ROOT)),
                "file_lean": file_lean_str,
                "thms": sib_thms,
                "labels": sib_labels,
                "label_slugs": sorted(sib_label_set),
                "unmarked": sib_unmarked,
                "closed": sib_closed,
            })
    if parent_has_inline or not siblings:
        parent_thms = len(LEAN_MARKER_RE.findall(parent_text))
        parent_label_set = {f"{m.group(1)}:{m.group(2)}"
                              for m in PAPER_LABEL_FULL_RE.finditer(parent_text)}
        siblings.append({
            "name": chapter_name,
            "sibling_id": parent_tex.stem,
            "file_paper": str(parent_tex.relative_to(ROOT)),
            "file_lean": file_lean_str,
            "thms": parent_thms,
            "labels": len(parent_label_set),
            "label_slugs": sorted(parent_label_set),
            "unmarked": max(0, len(parent_label_set) - parent_thms),
            "closed": False,
        })
    return siblings


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
    """Atomically pick the best non-locked sibling node, record it in
    LOCKS_FILE, and return a re-ordered top with locked sibling nodes
    demoted to the bottom.

    Lock granularity is the sibling `file_paper` path (not chapter
    `name`), so 12 concurrent workers can claim 12 different siblings of
    the same chapter without serializing. Concurrent invocations
    serialize on flock so each one sees the latest lock state.
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
        locked_keys = set(locks.keys())
        # Lock key = sibling file_paper (per-sibling granularity); fall
        # back to chapter name for any legacy entries that lack it.
        def _key(r: dict) -> str:
            return r.get("file_paper") or r.get("name", "")
        available = [r for r in ranked if _key(r) not in locked_keys]
        locked = [r for r in ranked if _key(r) in locked_keys]
        # Claim the new top-1 (the available[0]) for this caller
        if available:
            locks[_key(available[0])] = now + LOCK_TTL_SECONDS
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
    """Rank OPEN sibling fronts by transitive downstream impact.

    The graph is still chapter-level for closure / dep-readiness logic
    (a horizon's `\\closureat{<X>Up}{checkedCert|bridgeCert}` and its
    `\\<Dep>Up` references operate at chapter granularity). The ranking
    output is per-sibling: each chapter contributes one row PER OPEN
    SIBLING file under it. Workers can therefore claim distinct siblings
    of the same chapter without colliding on the cooldown lock.

    Score: `chapter_downstream` (kept raw so the magnet rule in
    `phase_b.txt` still sees a 71x lead when one exists). Tiebreakers:
    (1) prefer the chapter overall with fewer total thms; (2) within a
    chapter, prefer the sibling with fewer thms (closer to fresh
    coverage). This stably orders all sibling fronts of high-leverage
    chapters above siblings of low-leverage chapters, while letting
    concurrent workers spread across the chapter's sibling pool.
    """
    active_claimed = _read_active_claimed_labels()
    ranked: list[dict] = []
    for n, info in horizons.items():
        if n in SCHEMA_ONLY_HORIZONS:
            continue
        if info.get("closed"):
            continue
        if not deps_ready(n, horizons, threshold):
            continue
        chapter_down = downstream[n]
        chapter_thms = info["thms"]
        for sib in info.get("siblings", []):
            if sib.get("closed"):
                continue
            sib_unmarked_raw = sib.get("unmarked", 0)
            if sib_unmarked_raw <= 0:
                continue
            # Subtract paper-label-claims held by other in-flight rounds —
            # those are unavailable to this round so they shouldn't count
            # toward "available work" in the rank.
            sib_label_set = set(sib.get("label_slugs", []))
            sib_claimed = len(sib_label_set & active_claimed) if active_claimed else 0
            sib_effective_unmarked = max(0, sib_unmarked_raw - sib_claimed)
            if sib_effective_unmarked <= 0:
                continue
            # Sibling-level tiebreak: prefer fronts where most of the
            # remaining surface is unmarked (low markers / high effective
            # unmarked). Replaces the older chapter-level tiebreak which
            # didn't differentiate siblings within a chapter.
            sib_tiebreak = sib_effective_unmarked / (1.0 + sib["thms"])
            ranked.append({
                "name": n,
                "deps": info["deps"],
                "thms": chapter_thms,
                "closed_at": info.get("closed_at"),
                "closed": False,
                "downstream": chapter_down,
                "score": chapter_down,
                "tiebreak": round(sib_tiebreak, 2),
                # Sibling-level fields:
                "sibling_id": sib["sibling_id"],
                "sibling_thms": sib["thms"],
                "sibling_labels": sib.get("labels", 0),
                "sibling_unmarked": sib_unmarked_raw,
                "sibling_claimed": sib_claimed,
                "sibling_effective_unmarked": sib_effective_unmarked,
                "file_paper": sib["file_paper"],
                "file_lean": sib["file_lean"],
            })
    # Sort: prefer high downstream, then HIGH effective_unmarked (slots not
    # already claimed), then per-sibling tiebreak, then alphabetic.
    ranked.sort(key=lambda r: (
        -r["score"], -r["sibling_effective_unmarked"], -r["tiebreak"],
        r["name"], r["sibling_id"],
    ))
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
        "granularity": "sibling",
        "top": rolled[:25],
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
