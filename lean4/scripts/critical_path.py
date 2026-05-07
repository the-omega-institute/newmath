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
CLOSURESTATUS_BEGIN_RE = re.compile(
    r"\\begin\{closurestatus\}\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}"
)
CLOSURESTATUS_END_RE = re.compile(r"\\end\{closurestatus\}")
THEORYCLOSURE_RE = re.compile(r"\\theoryclosure\{\\(\w+)\}")
FORMALSTATUS_RE = re.compile(r"\\formalstatus\{\\(\w+)\}")
LEANTARGET_RE = re.compile(r"\\leantarget\{([^}]+)\}")
BRIDGESTATUS_RE = re.compile(r"\\bridgestatus\{(\w+)\}")
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")
PAPER_ROOT_DIR = ROOT / "papers" / "bedc"

CLOSURE_GRADE_ORDER = [
    "seedClosure", "obligationClosure", "scopedClosure",
    "publicClosure", "bridgedClosure", "matureClosure",
]
FORMAL_GRADE_ORDER = [
    "unformalizedV", "formalTargetV", "encodedDefV",
    "scaffoldCheckedV", "theoremCheckedV", "auditCleanV",
    "axiomCleanV", "bridgeCheckedV",
]
RETIREMENT_CLOSURE_THRESHOLD = "scopedClosure"
RETIREMENT_FORMAL_THRESHOLD = "theoremCheckedV"


def _grade_at_or_above(grade: str | None, threshold: str, order: list[str]) -> bool:
    if grade is None or grade not in order or threshold not in order:
        return False
    return order.index(grade) >= order.index(threshold)


def _grade_max(a: str | None, b: str | None, order: list[str]) -> str | None:
    """Pick the higher of two grade tokens by order index. None counts as below."""
    def idx(g):
        if g is None or g not in order:
            return -1
        return order.index(g)
    return a if idx(a) >= idx(b) else b


def _git_head_short() -> str:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--short=12", "HEAD"],
            cwd=str(ROOT), capture_output=True, text=True, check=False,
        )
        return out.stdout.strip() or "nohead"
    except Exception:
        return "nohead"


_objective_grades_cache: dict[str, str] | None = None


def load_objective_formal_grades() -> dict[str, str]:
    """Map each Lean qualified name to its OBJECTIVE formal grade derived
    from build artifacts (axiom-purity --strict + declaration inventory),
    NOT from closurestatus tokens written into the paper.

    Returns: {qualified_name: grade_token}. Grades reflect:
      - axiomCleanV  : in `pure` set of axiom-purity --strict --json
      - auditCleanV  : declared as theorem/lemma but not in pure set
      - encodedDefV  : declared as def / inductive / structure / class
      - formalTargetV: declared but kind unknown
      - (absent) -> caller treats as unformalizedV / no objective

    Cached per git HEAD under /tmp/bedc_objective_grades_<HEAD>.json so
    repeated codex rounds don't re-pay the cost of `lake env lean
    #print axioms` for 6000+ targets.
    """
    global _objective_grades_cache
    if _objective_grades_cache is not None:
        return _objective_grades_cache

    import tempfile
    head = _git_head_short()
    cache_path = Path(tempfile.gettempdir()) / f"bedc_objective_grades_{head}.json"
    if cache_path.exists():
        try:
            data = json.loads(cache_path.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                _objective_grades_cache = data
                return data
        except Exception:
            pass

    try:
        result = subprocess.run(
            ["python3", "lean4/scripts/bedc_ci.py",
             "axiom-purity", "--strict", "--json"],
            cwd=str(ROOT), capture_output=True, text=True, check=False,
        )
        if result.returncode == 0 and result.stdout.strip():
            payload = json.loads(result.stdout)
            pure_set = set(payload.get("pure", []))
        else:
            pure_set = set()
    except Exception:
        pure_set = set()

    # Reuse bedc_ci's declaration inventory to know each target's kind.
    try:
        sys_path_addition = str((ROOT / "lean4" / "scripts").resolve())
        import sys as _sys
        if sys_path_addition not in _sys.path:
            _sys.path.insert(0, sys_path_addition)
        from bedc_ci import build_declaration_inventory  # type: ignore
        declarations, _fields = build_declaration_inventory()
    except Exception:
        declarations = []

    grades: dict[str, str] = {}
    for d in declarations:
        qn = d.qualified_name
        if qn in pure_set:
            grades[qn] = "axiomCleanV"
        elif d.kind in ("theorem", "lemma"):
            grades[qn] = "auditCleanV"
        elif d.kind in ("def", "inductive", "structure", "class", "abbrev"):
            grades[qn] = "encodedDefV"
        else:
            grades[qn] = "formalTargetV"

    _objective_grades_cache = grades
    try:
        cache_path.write_text(json.dumps(grades), encoding="utf-8")
    except Exception:
        pass
    return grades


def normalize_name(stem: str) -> str:
    """Map paper file basename to canonical horizon key (lowercase)."""
    m = NAME_RE.match(stem)
    return m.group(1) if m else stem.lower()


def derive_lean_camel_case(paper_key: str, paper_text: str) -> str:
    """Recover the canonical CamelCase form of a horizon name.

    `paper_key` is the lowercase basename (e.g. "abgroup", "commring",
    "linearmap"). The naive .capitalize() pass yields "Abgroup",
    "Commring", "Linearmap" — wrong for the multi-word horizons. The
    paper text always references the horizon as `\\<X>Up`; we grep that
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


def is_chapter_retired_from_horizon(
    chapter_text: str, name: str
) -> tuple[bool, str | None, str | None, str | None, str | None, bool]:
    """Returns (retired, theory_token, formal_token, lean_target,
                  objective_formal_grade, formalstatus_drift,
                  bridge_token).

    `formal_token` is what the closurestatus block literally writes;
    `objective_formal_grade` is what the lean_target deserves under the
    current build (axiom-purity --strict pure -> axiomCleanV; declared
    theorem -> auditCleanV; def -> encodedDefV; etc.). When the token is
    strictly below the objective, the chapter is in `formalstatus_drift`
    and is NOT retired — codex needs to write the token up to match the
    objective so the paper labels reflect reality.
    """
    objective_grades = load_objective_formal_grades()
    for m in CLOSURESTATUS_BEGIN_RE.finditer(chapter_text):
        if m.group(1).lower() != name.lower():
            continue
        tail = chapter_text[m.end():]
        end = CLOSURESTATUS_END_RE.search(tail)
        body = tail[:end.start()] if end else tail
        tc_match = THEORYCLOSURE_RE.search(body)
        fs_match = FORMALSTATUS_RE.search(body)
        lt_match = LEANTARGET_RE.search(body)
        br_match = BRIDGESTATUS_RE.search(body)
        tc = tc_match.group(1) if tc_match else None
        fs = fs_match.group(1) if fs_match else None
        lt = (
            lt_match.group(1).replace("\\_", "_").strip()
            if lt_match else None
        )
        br = br_match.group(1).strip() if br_match else None
        objective_fs = objective_grades.get(lt) if lt else None
        token_idx = (FORMAL_GRADE_ORDER.index(fs)
                     if fs in FORMAL_GRADE_ORDER else -1)
        obj_idx = (FORMAL_GRADE_ORDER.index(objective_fs)
                   if objective_fs in FORMAL_GRADE_ORDER else -1)
        drift = obj_idx > token_idx
        effective_fs = _grade_max(fs, objective_fs, FORMAL_GRADE_ORDER)
        # Drift (token < objective) is informational ONLY; do NOT block
        # retire on it. A chapter that satisfies the closure + formal
        # thresholds is retired regardless of whether its written
        # `formalstatus` token is exactly equal to the objective grade.
        # Token-vs-objective sync is handled by a separate drift-fix
        # pass; coupling it to retire caused the entire retired set to
        # collapse to zero when objectives moved up to axiomCleanV
        # globally (since paper-side tokens are uniformly theoremCheckedV).
        retired = (
            _grade_at_or_above(tc, RETIREMENT_CLOSURE_THRESHOLD,
                                CLOSURE_GRADE_ORDER)
            and _grade_at_or_above(effective_fs,
                                    RETIREMENT_FORMAL_THRESHOLD,
                                    FORMAL_GRADE_ORDER)
        )
        return (retired, tc, fs, lt, objective_fs, drift, br)
    return (False, None, None, None, None, False, None)


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
        # `labels` counts paper obligation `\label{thm|def|...}` slugs in
        # the chapter's full include closure. Distinct from `thms` (lean
        # markers): paper writes obligations first, lean catches up
        # later. `deps_ready` uses `max(thms, labels)` so a chapter with
        # paper obligation content is treated as "ready" downstream
        # before its lean side has filled in markers — otherwise root
        # chapters with rich paper obligations but no lean markers stay
        # in dep-blocked limbo.
        labels = len({f"{m.group(1)}:{m.group(2)}"
                      for m in PAPER_LABEL_FULL_RE.finditer(full_text)})
        (retired, theory_grade, formal_grade, lean_target,
         objective_formal_grade, formalstatus_drift,
         bridge_token) = (
            is_chapter_retired_from_horizon(full_text, name)
        )
        closed_at = [theory_grade, formal_grade] if retired else None
        # Compute next-grade targets per axis. Used by phase B/C prompts to
        # pick the right "level transition" target shape for the round.
        theory_next = _next_grade(theory_grade, CLOSURE_GRADE_ORDER)
        formal_next = _next_grade(formal_grade, FORMAL_GRADE_ORDER)
        if formalstatus_drift:
            next_axis = "formalstatus_sync"
        else:
            next_axis = _select_next_axis(theory_grade, formal_grade)
        camel = derive_lean_camel_case(name, text)
        lean_file = DERIVED_DIR / f"{camel}Up.lean"
        siblings = _collect_siblings(tex, name, camel, lean_file)
        horizons[name] = {
            "name": name,
            "deps": sorted(deps),
            "thms": thms,
            "labels": labels,
            "closed_at": closed_at,
            "closed": retired,
            "closure_grounding": lean_target,
            "lean_target": lean_target,
            "theory_grade": theory_grade,
            "formal_grade": formal_grade,
            "theory_grade_next": theory_next,
            "formal_grade_next": formal_next,
            "objective_formal_grade": objective_formal_grade,
            "formalstatus_drift": formalstatus_drift,
            "bridge_token": bridge_token,
            "next_axis": next_axis,
            "next_grade_transition": _format_transition(
                theory_grade, formal_grade, theory_next, formal_next, next_axis,
                objective_formal_grade, formalstatus_drift
            ),
            "file_paper": str(tex.relative_to(ROOT)),
            "file_lean": str(lean_file.relative_to(ROOT)),
            "siblings": siblings,
        }
    return horizons


def _next_grade(current: str | None, order: list[str]) -> str | None:
    """Next-higher grade in `order` after `current`. None if at top or
    `current` is not in `order` (treat as needing the lowest grade)."""
    if current is None:
        return order[0] if order else None
    if current not in order:
        return order[0] if order else None
    i = order.index(current)
    if i + 1 >= len(order):
        return None
    return order[i + 1]


def _select_next_axis(theory: str | None, formal: str | None) -> str:
    """Choose which axis (theory_closure / formal_status) needs the next
    bump first. Strategy: pick the axis that is FARTHEST below its
    retirement threshold — the more lagging axis is the bottleneck for
    retirement. Ties go to formal (lean rounds dominate the dispatcher)."""
    def lag(grade, order, threshold):
        if grade is None:
            return len(order)  # "below the order" — max lag
        try:
            cur = order.index(grade)
        except ValueError:
            return len(order)
        try:
            tgt = order.index(threshold)
        except ValueError:
            return 0
        return max(0, tgt - cur)
    t_lag = lag(theory, CLOSURE_GRADE_ORDER, RETIREMENT_CLOSURE_THRESHOLD)
    f_lag = lag(formal, FORMAL_GRADE_ORDER, RETIREMENT_FORMAL_THRESHOLD)
    return "theory_closure" if t_lag > f_lag else "formal_status"


def _format_transition(theory_cur, formal_cur, theory_next, formal_next, axis,
                          objective_formal_grade=None, formalstatus_drift=False) -> str:
    """Human-readable string codex can plan against."""
    if axis == "formalstatus_sync":
        return (f"formalstatus_sync: token={formal_cur or '(none)'}"
                f" -> objective={objective_formal_grade or '(none)'}")
    if axis == "theory_closure":
        return f"theory: {theory_cur or '(none)'} -> {theory_next or '(top)'}"
    return f"formal: {formal_cur or '(none)'} -> {formal_next or '(top)'}"


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
            sib_closed = is_chapter_retired_from_horizon(
                sib_text, chapter_name
            )[0]
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
    """All declared deps must already have `>= threshold` of EITHER
    lean markers (`thms`) OR paper obligation labels (`labels`).

    Why max() instead of just `thms`: paper rounds write obligation
    `\\label{thm:...}` blocks ahead of lean rounds adding
    `\\leanchecked` markers. With strict `thms` check, a chapter
    with rich paper obligation surface (e.g. bundle: 9 \\begin{theorem}
    + 9 \\label) but 0 lean markers stays dep-blocked, blocking 5+
    downstream chapters from entering critical_path.top. By the time
    lean catches up the obligation surface may have moved on.

    Using max(thms, labels) treats paper-written obligations as
    "ready downstream" — the dep chapter has enough content that
    lean rounds can now form lean targets against it.
    """
    for d in horizons[name]["deps"]:
        if d not in horizons:
            continue  # external (e.g. a kernel object); ignore
        ready = max(
            horizons[d].get("thms", 0),
            horizons[d].get("labels", 0),
        )
        if ready < threshold:
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
    and dependency references operate at chapter granularity. The ranking
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
            # Distance from retirement (used in sort key — chapters
            # closer to (scoped, theoremChecked) get a small boost so the
            # tail closes faster while still respecting downstream order).
            t_lag = _grade_lag(info.get("theory_grade"),
                               CLOSURE_GRADE_ORDER, RETIREMENT_CLOSURE_THRESHOLD)
            f_lag = _grade_lag(info.get("formal_grade"),
                               FORMAL_GRADE_ORDER, RETIREMENT_FORMAL_THRESHOLD)
            chapter_lag = t_lag + f_lag
            ranked.append({
                "name": n,
                "deps": info["deps"],
                "thms": chapter_thms,
                "closed_at": info.get("closed_at"),
                "lean_target": info.get("lean_target"),
                "closed": False,
                "downstream": chapter_down,
                "score": chapter_down,
                "tiebreak": round(sib_tiebreak, 2),
                # Grade metadata (Phase 1 layered closure planning):
                "theory_grade": info.get("theory_grade"),
                "formal_grade": info.get("formal_grade"),
                "theory_grade_next": info.get("theory_grade_next"),
                "formal_grade_next": info.get("formal_grade_next"),
                "objective_formal_grade": info.get("objective_formal_grade"),
                "formalstatus_drift": info.get("formalstatus_drift", False),
                "next_axis": info.get("next_axis"),
                "next_grade_transition": info.get("next_grade_transition"),
                "chapter_grade_lag": chapter_lag,
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
    # Sort: prefer high downstream, then chapters CLOSER to retirement
    # (lower chapter_grade_lag = closer to scoped+theoremChecked → finish
    # them off so retirement frees critical-path slots), then HIGH
    # effective_unmarked, then per-sibling tiebreak, then alphabetic.
    ranked.sort(key=lambda r: (
        -r["score"],
        r["chapter_grade_lag"],
        -r["sibling_effective_unmarked"],
        -r["tiebreak"],
        r["name"], r["sibling_id"],
    ))
    return ranked


def _grade_lag(grade: str | None, order: list[str], threshold: str) -> int:
    """Number of grade steps between `grade` and `threshold` (≥0). Used by
    the sort key to prefer chapters closer to retirement so the tail
    closes faster."""
    if grade is None:
        return len(order)
    try:
        cur = order.index(grade)
    except ValueError:
        return len(order)
    try:
        tgt = order.index(threshold)
    except ValueError:
        return 0
    return max(0, tgt - cur)


def _inflight_paper_attack_chapters() -> set[str]:
    """Scan `.worktrees/paper_P*/` for working-tree changes touching
    `concrete_instances/<chapter>...` files. Returns the set of chapter
    names currently being attacked by in-flight paper rounds whose
    edits have NOT yet been committed.

    `_recent_paper_attack_chapter_counts` only sees committed work,
    so paper rounds dispatched within the last few minutes (still in
    Phase REVISE) are invisible to it. With paper=8 concurrent and
    only ~10 root-unblock candidates, multiple rounds dispatched in
    the same minute all picked the same `top_root_unblocks[0]`,
    each writing identical `\\label{thm:<chapter>-...}` content that
    collided at merge time.

    This in-flight scan complements the recency-counter: a chapter
    currently being edited by ANY paper worktree is rotated out of
    the next root_unblock dispatch, even before its first commit
    lands. Cheap (~10ms): one `git status --porcelain` per paper
    worktree.
    """
    chapters: set[str] = set()
    worktrees_dir = ROOT / ".worktrees"
    if not worktrees_dir.is_dir():
        return chapters
    pat = re.compile(
        r"concrete_instances/(?:\d+_)?([a-z][a-z0-9_]*?)(?:_namecert|/|\.tex)"
    )
    for wt in worktrees_dir.glob("paper_P*"):
        try:
            out = subprocess.run(
                ["git", "status", "--porcelain"],
                cwd=str(wt), capture_output=True, text=True,
                check=False, timeout=5,
            ).stdout
        except Exception:
            continue
        for line in out.splitlines():
            # Status format: 2-char status + space + path. May also have
            # rename arrows; just grab everything after first whitespace.
            parts = line.strip().split(None, 1)
            if len(parts) != 2:
                continue
            path = parts[1]
            m = pat.search(path)
            if m:
                chapters.add(m.group(1))
    return chapters


def _inflight_lean_attack_chapters() -> set[str]:
    """Same as _inflight_paper_attack_chapters but scans
    `.worktrees/round_R*/` for lean-side worktree edits to lean4/BEDC/
    or to paper closurestatus blocks. Used by bridge_candidates +
    formal_axis_top to avoid dispatching multiple lean rounds at the
    same chapter.
    """
    chapters: set[str] = set()
    worktrees_dir = ROOT / ".worktrees"
    if not worktrees_dir.is_dir():
        return chapters
    # Lean target name like BEDC.Derived.SheafUp or BEDC.Derived.SheafUp.X
    lean_pat = re.compile(r"lean4/BEDC/(?:[\w/]*?)/?(\w+)Up")
    paper_pat = re.compile(
        r"concrete_instances/(?:\d+_)?([a-z][a-z0-9_]*?)(?:_namecert|/|\.tex)"
    )
    for wt in worktrees_dir.glob("round_R*"):
        try:
            out = subprocess.run(
                ["git", "status", "--porcelain"],
                cwd=str(wt), capture_output=True, text=True,
                check=False, timeout=5,
            ).stdout
        except Exception:
            continue
        for line in out.splitlines():
            parts = line.strip().split(None, 1)
            if len(parts) != 2:
                continue
            path = parts[1]
            m = lean_pat.search(path)
            if m:
                chapters.add(m.group(1).lower())
            m2 = paper_pat.search(path)
            if m2:
                chapters.add(m2.group(1))
    return chapters


def _recent_paper_attack_chapter_counts(window_minutes: int = 30) -> dict[str, int]:
    """Count, per chapter, how many DISTINCT recent commits modified
    files under that chapter's paper paths.

    Used to dedupe `top_root_unblocks`: if 6 paper rounds in the last
    30 min all already attacked `manifold`, the chapter probably has
    enough in-flight work; rotate it out of the suggestion list so
    other root chapters (hilbert / topology / numfield) get airtime.
    Without this, v3.3's HARD GATE pulls every paper round to the
    same top_root_unblocks[0] entry, producing duplicate-label storms
    on merge. (Observed: 18/30 paper targets all attacked `manifold`
    in a recent 2h window; 8 dup-label audit fails per round followed.)

    Path → chapter mapping examples:
      papers/bedc/parts/concrete_instances/74_manifold_namecert_construction.tex
        → "manifold"
      papers/bedc/parts/concrete_instances/manifold/singleton_empty_chart.tex
        → "manifold"
    """
    counts: dict[str, int] = {}
    try:
        out = subprocess.run(
            ["git", "log", "--all",
             f"--since={window_minutes} minutes ago",
             "--name-only", "--pretty=format:%H END_OF_COMMIT"],
            cwd=str(ROOT), capture_output=True, text=True,
            check=True, timeout=10,
        ).stdout
    except Exception:
        return counts
    seen_in_commit: set[str] = set()
    for line in out.splitlines():
        if "END_OF_COMMIT" in line or not line.strip():
            for c in seen_in_commit:
                counts[c] = counts.get(c, 0) + 1
            seen_in_commit = set()
            continue
        # Match either `<n>_<chapter>_namecert_*` (numbered hub or sibling)
        # or `<chapter>/<sibling>.tex` (subdirectory under concrete_instances).
        m = re.search(
            r"concrete_instances/(?:\d+_)?([a-z][a-z0-9_]*?)(?:_namecert|/|\.tex)",
            line,
        )
        if m:
            # Strip trailing `_namecert_*` / sibling suffixes so the matched
            # token is the canonical lowercase chapter name.
            seen_in_commit.add(m.group(1))
    for c in seen_in_commit:
        counts[c] = counts.get(c, 0) + 1
    return counts


def compute_root_unblocks(horizons: dict[str, dict],
                            threshold: int,
                            *, recent_attack_threshold: int = 1) -> list[dict]:
    """Identify chapters whose `thms < threshold` are blocking the most
    downstream chapters from becoming `deps_ready`. These are the
    "root-of-tree" stubs that paper P-rounds should attack first to
    unblock large fan-outs.

    For each candidate root R (open, non-schema, `thms < threshold`),
    count how many OTHER open non-schema chapters M satisfy:
      - R ∈ M.deps
      - every other dep of M (besides R) is already at `thms >= threshold`
    i.e. R is the SINGLE remaining blocker for M. Lifting R to ready
    immediately unblocks `unblock_count` downstream chapters.

    Recency filter: chapters that already have
    `recent_attack_threshold` or more commits in the last 30 min are
    rotated OUT of the output, so concurrent paper rounds spread their
    attention across the root tree instead of dogpiling the top entry.
    `recent_attack_threshold=1` empirically required: codex deterministically
    writes the SAME obligation labels for the same chapter+task prompt,
    so even 2 concurrent rounds attacking the same root chapter produce
    duplicate `\\label{thm:<chapter>-...}` collisions. Threshold=1 means
    a chapter is rotated out the moment one commit lands; with paper=8
    workers, this still leaves enough chapters in rotation as long as
    `top_root_unblocks` has at least ~10 entries.

    Returns sorted list `[{name, thms, deps, unblock_count, file_paper,
    recent_attacks, inflight}, ...]` descending by unblock_count, only entries
    with `unblock_count > 0`, `recent_attacks < recent_attack_threshold`,
    AND `not inflight` (some other paper worktree is currently editing).
    """
    recent = _recent_paper_attack_chapter_counts(window_minutes=30)
    inflight = _inflight_paper_attack_chapters()
    candidates: list[dict] = []
    for n, info in horizons.items():
        if info.get("closed"):
            continue
        if n in SCHEMA_ONLY_HORIZONS:
            continue
        if info.get("thms", 0) >= threshold:
            continue
        # Count downstream chapters where n is the SINGLE remaining blocker.
        unblock = 0
        for m, mh in horizons.items():
            if m == n or mh.get("closed"):
                continue
            if m in SCHEMA_ONLY_HORIZONS:
                continue
            if n not in mh.get("deps", []):
                continue
            other_blockers = 0
            for d in mh["deps"]:
                if d == n:
                    continue
                if d not in horizons:
                    continue  # external (kernel) — assume ready
                if horizons[d].get("thms", 0) < threshold:
                    other_blockers += 1
            if other_blockers == 0:
                unblock += 1
        if unblock <= 0:
            continue
        if n in inflight:
            # Another paper worktree is currently editing this chapter;
            # any new round picking it would write duplicate labels.
            continue
        recent_count = recent.get(n, 0)
        if recent_count >= recent_attack_threshold:
            # Already getting heavy attention from concurrent rounds;
            # rotate out so other roots get a turn.
            continue
        candidates.append({
            "name": n,
            "thms": info.get("thms", 0),
            "deps": info.get("deps", []),
            "unblock_count": unblock,
            "recent_attacks": recent_count,
            "file_paper": info.get("file_paper"),
        })
    candidates.sort(key=lambda r: (-r["unblock_count"], r["thms"], r["name"]))
    return candidates


# `theory_closure` upgrade chain. Each entry is a `(from_grade, to_grade)`
# transition that paper P-rounds drive via `closure_mark` targets. The
# upgrade chain has historically stalled past `scopedClosure` because
# critical_path retired chapters from `top` and paper never saw them again.
# `compute_transition_candidates` re-exposes them as a SECONDARY priority
# track: every paper round picks one transition (round-number rotation in
# phase_review.txt) and operates on its top candidate.
THEORY_TRANSITION_CHAIN: list[tuple[str | None, str]] = [
    (None, "seedClosure"),
    ("seedClosure", "obligationClosure"),
    ("obligationClosure", "scopedClosure"),
    ("scopedClosure", "publicClosure"),
    ("publicClosure", "bridgedClosure"),
    ("bridgedClosure", "matureClosure"),
]


def compute_transition_candidates(horizons: dict[str, dict],
                                    downstream: dict[str, int],
                                    from_grade: str | None,
                                    to_grade: str,
                                    *, max_results: int = 5) -> list[dict]:
    """Return chapters at `theory_grade == from_grade` ranked by upgrade
    impact (higher transitive downstream first). Used for the
    transition-rotation upgrade chain in `phase_review.txt`."""
    candidates: list[dict] = []
    for n, info in horizons.items():
        if n in SCHEMA_ONLY_HORIZONS:
            continue
        # Match the chapter's CURRENT theory_grade. None means no
        # closurestatus block yet (the (none) → seedClosure step).
        if info.get("theory_grade") != from_grade:
            continue
        candidates.append({
            "name": n,
            "from_grade": from_grade,
            "to_grade": to_grade,
            "downstream": downstream.get(n, 0),
            "thms": info.get("thms", 0),
            "labels": info.get("labels", 0),
            "formal_grade": info.get("formal_grade"),
            "file_paper": info.get("file_paper"),
            "lean_target": info.get("lean_target"),
        })
    # Sort: higher fan-out first; tie-break by labels (more obligation
    # surface = closer to next-grade requirements); then by name.
    candidates.sort(
        key=lambda r: (-r["downstream"], -r["labels"], r["name"]),
    )
    return candidates[:max_results]


def main() -> int:
    horizons = extract_horizons()
    downstream = transitive_downstream(horizons)

    # Read the strict threshold from .pipeline_parallel.json (default 5).
    strict = read_deps_ready_threshold()

    # Adaptive two-stage relax:
    #   Stage 1 — supply-aware: walk strict → THRESHOLD_FLOOR (default 3),
    #     pick the highest threshold whose ranked output is >= MIN_TOP_SIZE.
    #     This keeps quality high (dep >= 3 thms still required) but
    #     ensures lean has at least MIN_TOP_SIZE sibling fronts to claim,
    #     avoiding the supply-starved state where lean=top_size is forced
    #     down to 1-2 workers.
    #   Stage 2 — emergency: if even THRESHOLD_FLOOR yields empty, descend
    #     to 1 (the legacy "wedged at empty top" rescue).
    MIN_TOP_SIZE = 5
    THRESHOLD_FLOOR = 3

    relaxed_at = None
    ranked: list[dict] = []
    for t in range(strict, THRESHOLD_FLOOR - 1, -1):
        candidate = _rank_at_threshold(horizons, downstream, t)
        if len(candidate) >= MIN_TOP_SIZE:
            ranked = candidate
            if t < strict:
                relaxed_at = t
            break
        # Keep the best non-empty seen so far (largest top), to use if no
        # threshold reaches MIN_TOP_SIZE.
        if len(candidate) > len(ranked):
            ranked = candidate
            relaxed_at = t if t < strict else None

    # Stage 2: if nothing at all from THRESHOLD_FLOOR..strict, fall through.
    if not ranked:
        for t in range(THRESHOLD_FLOOR - 1, 0, -1):
            candidate = _rank_at_threshold(horizons, downstream, t)
            if candidate:
                ranked = candidate
                relaxed_at = t
                break

    rolled = _claim_top_with_cooldown(ranked)

    closed_count: dict[str, int] = {}
    open_count = 0
    for info in horizons.values():
        c = info.get("closed_at")
        if info.get("closed") and isinstance(c, list) and len(c) == 2:
            key = f"{c[0]}/{c[1]}"
            closed_count[key] = closed_count.get(key, 0) + 1
        elif not info.get("closed"):
            open_count += 1

    # Compute root-unblock candidates against the EFFECTIVE threshold
    # (post-relaxation) so the suggestion list matches what _rank_at_threshold
    # actually filtered against.
    effective_threshold = relaxed_at if relaxed_at is not None else strict
    root_unblocks = compute_root_unblocks(horizons, effective_threshold)

    # Theory-closure transition chain: 6 transitions from (none) →
    # seedClosure all the way to bridgedClosure → matureClosure. Each
    # gets its own ranked top list so paper P-rounds can rotate
    # attention across the chain instead of dogpiling the (none) →
    # first-register transition (which had been ~95% of all
    # closure_mark commits).
    transition_keys = [
        "to_seed", "to_obligation", "to_scoped",
        "to_public", "to_bridged", "to_mature",
    ]
    top_transitions = {}
    for key, (from_grade, to_grade) in zip(transition_keys, THEORY_TRANSITION_CHAIN):
        top_transitions[key] = compute_transition_candidates(
            horizons, downstream, from_grade, to_grade,
        )

    # drift_chapters: chapters where the closurestatus block writes
    # a `\formalstatus{X}` token that is strictly LOWER than the
    # objective grade derivable from build artifacts (axiom-purity
    # --strict / declaration kind). The chapter is functionally fine
    # but its paper-side label undersells what Lean has actually
    # achieved. Paper P-rounds should sync the token to the objective
    # via a `closure_mark` target that rewrites the `\formalstatus{...}`
    # line. Currently the bulk are `theoremCheckedV` tokens whose
    # Lean targets are in fact `axiomCleanV` (no Classical.choice /
    # Quot.sound / propext anywhere in the dependency closure).
    # Anti-dogpile: a 1-line drift sync target on the same chapter
    # cannot be safely run by 5 concurrent paper workers — every later
    # round produces an identical merge conflict. Reuse the existing
    # in-flight + recent-attack filters used for top_root_unblocks.
    inflight_paper = _inflight_paper_attack_chapters()
    recent_paper = _recent_paper_attack_chapter_counts(window_minutes=15)
    drift_chapters_full = []
    for info in horizons.values():
        if not info.get("formalstatus_drift"):
            continue
        n = info["name"]
        if n in inflight_paper:
            continue
        if recent_paper.get(n, 0) >= 1:
            continue
        drift_chapters_full.append({
            "name": n,
            "file_paper": info["file_paper"],
            "file_lean": info["file_lean"],
            "lean_target": info.get("lean_target"),
            "theory_grade": info.get("theory_grade"),
            "formal_grade_token": info.get("formal_grade"),
            "objective_formal_grade": info.get("objective_formal_grade"),
            "thms": info.get("thms", 0),
        })
    # Rank: prefer chapters with higher objective grade (axiomCleanV
    # over auditCleanV), then by thms (richer chapters first).
    _OBJ_RANK = {"axiomCleanV": 4, "auditCleanV": 3,
                 "encodedDefV": 2, "formalTargetV": 1}
    drift_chapters_full.sort(
        key=lambda c: (_OBJ_RANK.get(c.get("objective_formal_grade") or "", 0),
                       c.get("thms", 0)),
        reverse=True,
    )
    # Anti-dogpile via per-call shuffle of the surfaced top-25. With
    # 10 paper workers all calling critical_path within a few seconds,
    # the deterministic top-N collapses every round to picking the
    # same 1-2 chapters; the dedup machinery then drops 9/10 rounds.
    # Seeded by os.urandom so different paper-round dispatches see
    # different orderings, while a single round's call sees a stable
    # ordering inside its own JSON.
    import random as _rand
    surfaced = drift_chapters_full[:25]
    _rand.Random().shuffle(surfaced)
    drift_chapters = surfaced

    # bridge_candidates: chapters that have reached the top of the
    # theory axis (matureClosure) AND whose Lean target is already at
    # axiomCleanV objective, but whose `closurestatus.\bridgestatus`
    # field is still `none` (or absent). These chapters are ready for
    # the final lean upgrade — write a `StdBridge` Lean theorem
    # connecting the chapter's concrete BHist instance to its abstract
    # `<X>Up` schema, then paper P-rounds flip `\bridgestatus{none}` to
    # `\bridgestatus{bridgeChecked}` and update `\formalstatus` to
    # `\bridgeCheckedV`. Lean R-rounds should preferentially pick
    # bridge_candidates[0..2] when no urgent formal-axis work in `top`
    # is left.
    # Detect existing <X>Up_StdBridge theorems already written under
    # lean4/BEDC/Derived/. A chapter whose StdBridge exists in the
    # build is "lean-side bridged"; the only remaining work is the
    # paper-side closurestatus sync.
    stdbridge_lean_chapters: set[str] = set()
    for d in (ROOT / "lean4" / "BEDC" / "Derived").rglob("*.lean"):
        try:
            text = d.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        for m in re.finditer(
            r"^\s*(?:theorem|lemma)\s+(\w+)Up_StdBridge\b",
            text, flags=re.MULTILINE,
        ):
            stdbridge_lean_chapters.add(m.group(1).lower())

    bridge_candidates_full = []
    bridge_sync_pending_full = []
    for info in horizons.values():
        tg = info.get("theory_grade")
        obj = info.get("objective_formal_grade")
        br = info.get("bridge_token")
        n = info["name"]
        if tg != "matureClosure":
            continue
        # Already fully done on both sides.
        if br in ("bridgeChecked", "bridgeCheckedV"):
            continue
        entry = {
            "name": n,
            "file_paper": info["file_paper"],
            "file_lean": info["file_lean"],
            "lean_target": info.get("lean_target"),
            "bridge_token": br,
            "thms": info.get("thms", 0),
        }
        if n in stdbridge_lean_chapters:
            # Lean side already has <X>Up_StdBridge. Paper just needs to
            # update bridgestatus + formalstatus to bridgeCheckedV.
            # No objective gate here — the StdBridge theorem itself is
            # the verification that work is done.
            entry["lean_stdbridge_present"] = True
            bridge_sync_pending_full.append(entry)
        elif obj == "axiomCleanV":
            # Lean target is already axiomCleanV but no StdBridge yet —
            # this is real lean work to do (write the StdBridge theorem).
            bridge_candidates_full.append(entry)
        # else: lean target below axiomCleanV AND no StdBridge — not a
        # bridge candidate yet (drift sync / formal_axis_top first).
    # Filter in-flight + recent (lean side: scan .worktrees/round_R*/)
    inflight_lean = _inflight_lean_attack_chapters()
    bridge_candidates_full = [
        c for c in bridge_candidates_full
        if c["name"] not in inflight_lean
    ]
    bridge_candidates_full.sort(key=lambda c: c.get("thms", 0), reverse=True)
    bridge_candidates = bridge_candidates_full[:10]

    # bridge_sync_pending uses paper-side in-flight filter (it's a
    # paper P-round task: edit the chapter's closurestatus block).
    bridge_sync_pending_full = [
        c for c in bridge_sync_pending_full
        if c["name"] not in inflight_paper
    ]
    bridge_sync_pending_full.sort(key=lambda c: c.get("thms", 0), reverse=True)
    bridge_sync_pending = bridge_sync_pending_full[:10]

    # formal_axis_top: chapters whose theory axis is mature OR whose
    # paper closurestatus block records a non-trivial theory_grade,
    # but whose formal_grade token is < theoremCheckedV (i.e. lean
    # really hasn't done the work yet — distinct from drift_chapters
    # where lean HAS done it but paper undersells). Lean rounds should
    # advance these chapters' formal axis. Currently mostly chapters
    # where paper wrote `\formalstatus{\unformalizedV}` while having a
    # mature theory body (sheaf, projectivespace, etc.).
    formal_axis_top_full = []
    _BELOW_TC = {"unformalizedV", "formalTargetV",
                 "encodedDefV", "scaffoldCheckedV"}
    for info in horizons.values():
        tg = info.get("theory_grade")
        fg = info.get("formal_grade")
        if not tg:
            continue  # no closurestatus block — covered by main `top`
        if fg not in _BELOW_TC:
            continue
        formal_axis_top_full.append({
            "name": info["name"],
            "file_paper": info["file_paper"],
            "file_lean": info["file_lean"],
            "theory_grade": tg,
            "formal_grade_token": fg,
            "thms": info.get("thms", 0),
            "labels": info.get("labels", 0),
        })
    formal_axis_top_full = [
        c for c in formal_axis_top_full
        if c["name"] not in inflight_lean
    ]
    # Rank: chapters with high theory grade + many labels first
    _TG_RANK = {"matureClosure": 6, "bridgedClosure": 5,
                "publicClosure": 4, "scopedClosure": 3,
                "obligationClosure": 2, "seedClosure": 1}
    formal_axis_top_full.sort(
        key=lambda c: (_TG_RANK.get(c.get("theory_grade") or "", 0),
                       c.get("labels", 0)),
        reverse=True,
    )
    formal_axis_top = formal_axis_top_full[:10]

    payload = {
        "computed_at": datetime.now(timezone.utc).isoformat(),
        "deps_ready_threshold": strict,
        "deps_ready_threshold_used": effective_threshold,
        "deps_ready_relaxed": relaxed_at is not None,
        "closed_horizons": closed_count,
        "open_horizons": open_count,
        "drift_chapters_total": len(drift_chapters_full),
        "bridge_candidates_total": len(bridge_candidates_full),
        "bridge_sync_pending_total": len(bridge_sync_pending_full),
        "bridge_sync_pending": bridge_sync_pending,
        "formal_axis_top_total": len(formal_axis_top_full),
        "granularity": "sibling",
        "top": rolled[:25],
        "top_root_unblocks": root_unblocks[:10],
        "top_transitions": top_transitions,
        "drift_chapters": drift_chapters,
        "bridge_candidates": bridge_candidates,
        "formal_axis_top": formal_axis_top,
    }
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
