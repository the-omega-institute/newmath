#!/usr/bin/env python3
"""Critical-path discovery for BEDC derived horizon coverage.

Picks the next domains Phase B should attack: high downstream impact, low
current implementation, dependencies already implemented. Used as a HARD
GATE in `lean4/scripts/prompts/phase_b.txt` so codex stops re-saturating
the same five domains and starts opening new fronts.

Run with no arguments. Output is JSON to stdout.
"""

from __future__ import annotations

import argparse
import bisect
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
_THEOREM_ENVS_CACHE_PATH = Path("/tmp/.bedc_cp_theorem_envs_cache.json")
_LEAN_DECLS_CACHE_PATH = Path("/tmp/.bedc_cp_lean_decls_cache.json")
_CACHE_ENABLED = True

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


def read_paper_priority_config() -> dict[str, object]:
    mode = "free"
    strength = 0.0
    try:
        if PARALLEL_CONFIG_FILE.exists():
            data = json.loads(PARALLEL_CONFIG_FILE.read_text(encoding="utf-8"))
            mode = str(data.get("paper_priority_mode", mode)).strip() or "free"
            strength = float(data.get("paper_priority_strength", strength))
    except Exception:
        mode = "free"
        strength = 0.0
    if mode != "human_metacic":
        strength = 0.0
    return {
        "paper_priority_mode": mode,
        "paper_priority_strength": round(max(0.0, min(strength, 1.0)), 4),
    }


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
    # All previously banned chapters (abgroup / group / monoid / ring /
    # commring / field / module / vecspace / linearmap / matrix /
    # polynomial / fps / lattice / totalorder / preorder / poset)
    # have been verified to carry concrete singleton-history pinning
    # (Carrier := UnaryHistory, mul := Cont, le := PreorderPrefixLE,
    # etc.) so the pipeline can produce BHist-anchored proofs without
    # reverting to parametric-operator schema. phase_d_lint.py +
    # parameter-echo gates catch regressions, so re-banning is
    # unnecessary. The set stays empty until a NEW chapter is added
    # that genuinely lacks concrete pinning.
}

NAME_RE = re.compile(r"^\d+_([a-z][a-z0-9_]*?)_namecert_construction\.tex$")
UP_REF_RE = re.compile(r"\\?([A-Z][A-Za-z]*)Up\b")
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef)\{")
PAPER_LABEL_RE = re.compile(r"\\label\{(thm|def|lem|prop|cor):")
PAPER_LABEL_FULL_RE = re.compile(r"\\label\{(thm|def|lem|prop|cor):([^}]+)\}")
NOTCLAIMED_RE = re.compile(r"\\notclaimed\{([^}]*)\}", re.DOTALL)
# Legacy regex retained for compat (some callers may still reference it),
# but `_has_induction_proof` below is the canonical fast path.
INDUCTION_PROOF_RE = re.compile(
    r"\\begin\{proof\}.*?(?:induct|case analysis).*?\\end\{proof\}",
    re.IGNORECASE | re.DOTALL,
)
# Catastrophic-regex avoidance: the old INDUCTION_PROOF_RE.search() on
# a 491KB chapter with `re.DOTALL` + lazy `.*?` + alternation prefix
# overlap (induction ⊂ induct, structural induction ⊂ induct) took 20s
# per chapter, and `compute_paper_priority_surfaces` ran it on ~100
# `\origin{human}` chapters → 150s+ total. The semantic intent is "is
# there any induction/case-analysis proof in this chapter?" — a fast
# substring check captures essentially the same signal at zero cost.
_INDUCTION_KEYWORDS = ("induct", "case analysis")


def _has_induction_proof(text: str) -> bool:
    """Fast O(N) substring approximation of the legacy regex. Returns
    True iff the chapter contains a `\\begin{proof}` block AND any
    induction/case-analysis keyword anywhere in the text. The keyword
    is not strictly required to be inside the proof block — but as a
    priority-surface heuristic (used only by `_has_human_derivation_gap`
    to suppress chapters whose human derivation appears to already
    induct/case-split), the loss of strict scoping is acceptable and
    avoids 20s/chapter catastrophic backtracking.
    """
    if "\\begin{proof}" not in text:
        return False
    lowered = text.lower()
    return any(k in lowered for k in _INDUCTION_KEYWORDS)

METACIC_RE = re.compile(r"metacic|MetaCIC|BEDC\.MetaCIC", re.IGNORECASE)
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

_LEAN_BASE_WEIGHTS = {
    "top": 0.50,
    "formal_axis_top": 0.25,
    "unformalized_top": 0.15,
    "carrier_isomorphism_capstone": 0.10,
}
_PAPER_BASE_WEIGHTS = {
    "top": 0.40,
    "top_root_unblocks": 0.30,
    "closure_mark": 0.20,
    "carrier_isomorphism_capstone": 0.10,
}
_PAPER_PRIORITY_BASE = {
    "human_derivation_gap": 0.8235,
    "metacic_priority": 0.1765,
}
_HUMAN_CANONICAL_TERMS = (
    "canonical", "complete", "completion", "cauchy", "banach",
    "fixed point", "quotient", "choice", "host equality", "limit",
    "compact", "series", "uniform", "metric", "classical",
)
CLOSUREAT_RE = re.compile(r"\\closureat\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}\{(\w+)\}")
CLOSUREAT_TO_GRADE = {
    "seedStr": "seedClosure",
    "obligationStr": "obligationClosure",
    "scopedStr": "scopedClosure",
    "publicStr": "publicClosure",
    "bridgedStr": "bridgedClosure",
    "matureStr": "matureClosure",
}


def _normalize_weights(weights: dict[str, float]) -> dict[str, float]:
    total = sum(v for v in weights.values() if v > 0)
    if total <= 0:
        count = len(weights) or 1
        return {k: round(1.0 / count, 4) for k in weights}
    return {k: round(max(0.0, v) / total, 4) for k, v in weights.items()}


def _cap_against_base(value: float, base_value: float) -> float:
    return min(base_value * 1.5, max(base_value * 0.5, value))


def _compute_consumption_60min() -> dict[str, int]:
    """Parse recent codex-auto-dev commits and infer target source counts."""
    sources = {
        "top": 0,
        "formal_axis_top": 0,
        "unformalized_top": 0,
        "top_root_unblocks": 0,
        "closure_mark": 0,
        "carrier_isomorphism_capstone": 0,
    }
    subjects: list[str] = []
    for branch in ("codex-auto-dev", "origin/codex-auto-dev", "HEAD"):
        try:
            result = subprocess.run(
                ["git", "log", branch, "--since=60 minutes ago",
                 "--no-merges", "--pretty=format:%s"],
                cwd=str(ROOT),
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )
        except Exception:
            continue
        if result.returncode == 0:
            subjects = [
                line.strip()
                for line in result.stdout.splitlines()
                if line.strip()
            ]
            break
    for subject in subjects:
        s = subject.lower()
        if re.search(r"carrier[-_ ]?isomorphism|capstone", s):
            sources["carrier_isomorphism_capstone"] += 1
        elif re.search(r"closure[_ -]?mark|closureat|drift|bridge sync|formalstatus|closurestatus", s):
            sources["closure_mark"] += 1
        elif re.search(r"root[-_ ]?unblock|root_unblocks", s):
            sources["top_root_unblocks"] += 1
        elif re.search(r"formal[-_ ]?axis|tastegate|bridge .*schema|axiomclean->bridgecheck", s):
            sources["formal_axis_top"] += 1
        elif re.search(r"unformalized|paper theorem|missing theorem|prove .*label", s):
            sources["unformalized_top"] += 1
        elif re.search(r"\b[RP]\d+:", subject) or re.search(r"\b(lean|paper|formaliz|prove|review|revise|chapter|theory)\b", s):
            sources["top"] += 1
    return sources


def _adjust_dispatch_weights(
    base: dict[str, float],
    supply: dict[str, int],
    consumption: dict[str, int],
) -> dict[str, float]:
    active = {
        key: weight
        for key, weight in base.items()
        if supply.get(key, 0) > 0 and weight > 0
    }
    if not active:
        return {key: 0.0 for key in base}

    total_rounds = sum(consumption.get(key, 0) for key in base)
    adjusted = dict(active)
    if total_rounds > 0:
        for key, weight in active.items():
            expected = weight * total_rounds
            factor = 1.0
            if consumption.get(key, 0) > expected * 1.5:
                factor = 0.7
            elif consumption.get(key, 0) < expected * 0.5:
                factor = 1.2
            adjusted[key] = _cap_against_base(weight * factor, base[key])

    normalized_active = _normalize_weights(adjusted)
    return {key: normalized_active.get(key, 0.0) for key in base}


def _dispatch_advice(side: str, weights: dict[str, float], supply: dict[str, int]) -> str:
    available = [
        (key, weight)
        for key, weight in weights.items()
        if supply.get(key, 0) > 0 and weight > 0
    ]
    if not available:
        return "No currently supplied source; use critical_path fallback gates."
    top = sorted(available, key=lambda item: item[1], reverse=True)[:2]
    if side == "lean":
        parts = [f"Pick {1 if weight < 0.34 else 2} of 3 from {key}" for key, weight in top]
        if weights.get("carrier_isomorphism_capstone", 0) >= 0.10 and supply.get("carrier_isomorphism_capstone", 0):
            parts.append("Consider 1 capstone draft if other sources are blocked")
    else:
        parts = [f"Pick {'2' if weight >= 0.34 else '1'} of 5 from {key}" for key, weight in top]
        if weights.get("carrier_isomorphism_capstone", 0) >= 0.10 and supply.get("carrier_isomorphism_capstone", 0):
            parts.append("Reserve at most 1 capstone NameCert seed when compatible with hard gates")
    return ". ".join(parts) + "."


def _compute_dispatch_weights(
    supply_lean: dict[str, int],
    supply_paper: dict[str, int],
    consumption: dict[str, int],
    base_weights_lean: dict[str, float],
    base_weights_paper: dict[str, float],
    capstone_candidate: dict | None = None,
    capstone_coverage: dict | None = None,
    paper_priority_config: dict[str, object] | None = None,
) -> dict[str, dict]:
    """Compute supply- and consumption-adjusted per-side weights."""
    lean_weights = _adjust_dispatch_weights(base_weights_lean, supply_lean, consumption)
    priority_config = paper_priority_config or {
        "paper_priority_mode": "free",
        "paper_priority_strength": 0.0,
    }
    priority_strength = float(priority_config.get("paper_priority_strength", 0.0) or 0.0)
    priority_strength = max(0.0, min(priority_strength, 1.0))
    if priority_strength > 0:
        regular_base = {
            key: value * (1.0 - priority_strength)
            for key, value in base_weights_paper.items()
        }
        priority_base = {
            key: value * priority_strength
            for key, value in _PAPER_PRIORITY_BASE.items()
        }
        paper_base_effective = {**regular_base, **priority_base}
    else:
        paper_base_effective = dict(base_weights_paper)
    paper_weights = _adjust_dispatch_weights(paper_base_effective, supply_paper, consumption)
    return {
        "lean": {
            "weights": lean_weights,
            "supply": supply_lean,
            "consumption_60min": {key: consumption.get(key, 0) for key in base_weights_lean},
            "capstone_candidate": capstone_candidate,
            "capstone_coverage": capstone_coverage,
            "advice": _dispatch_advice("lean", lean_weights, supply_lean),
        },
        "paper": {
            "weights": paper_weights,
            "supply": supply_paper,
            "consumption_60min": {key: consumption.get(key, 0) for key in paper_base_effective},
            "capstone_candidate": capstone_candidate,
            "capstone_coverage": capstone_coverage,
            "priority_config": priority_config,
            "advice": _dispatch_advice("paper", paper_weights, supply_paper),
        },
    }


def _count_closure_mark_candidates() -> int:
    """Count chapters where legacy closure marks outrun closurestatus."""
    count = 0
    for tex in sorted(NAMECERT_GLOB.glob("*_namecert_construction.tex")):
        name = normalize_name(tex.name)
        text = _read_chapter_recursive(tex)
        theory_grade = None
        for m in CLOSURESTATUS_BEGIN_RE.finditer(text):
            if m.group(1).lower() != name.lower():
                continue
            tail = text[m.end():]
            end = CLOSURESTATUS_END_RE.search(tail)
            body = tail[:end.start()] if end else tail
            tc_match = THEORYCLOSURE_RE.search(body)
            if tc_match:
                theory_grade = tc_match.group(1)
            break
        closure_grades = [
            CLOSUREAT_TO_GRADE[m.group(2)]
            for m in CLOSUREAT_RE.finditer(text)
            if m.group(1).lower() == name.lower() and m.group(2) in CLOSUREAT_TO_GRADE
        ]
        if not closure_grades:
            continue
        max_closureat = max(closure_grades, key=CLOSURE_GRADE_ORDER.index)
        theory_idx = (
            CLOSURE_GRADE_ORDER.index(theory_grade)
            if theory_grade in CLOSURE_GRADE_ORDER else -1
        )
        closureat_idx = CLOSURE_GRADE_ORDER.index(max_closureat)
        if closureat_idx > theory_idx:
            count += 1
    return count


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
            timeout=5,
        )
        return out.stdout.strip() or "nohead"
    except Exception:
        return "nohead"


_objective_grades_cache: dict[str, str] | None = None
_carrier_isomorphism_cache: dict | None = None

_ARITY_NAME = {
    1: "Mono",
    2: "Di",
    3: "Tri",
    4: "Tetra",
    5: "Penta",
    6: "Hexa",
    7: "Hepta",
    8: "Octa",
    9: "Nona",
    10: "Deca",
    11: "Hendeca",
    12: "Dodeca",
}

_GENERIC_NAME_TOKENS = {
    "Up",
    "Name",
    "Cert",
    "NameCert",
    "Taste",
    "Gate",
    "TasteGate",
    "Carrier",
    "Chapter",
    "BHist",
}


def _shape_summary(shape: object) -> str:
    """Compact phase-2 toEventFlow shape for critical_path JSON."""
    if not isinstance(shape, list) or not shape:
        return "unparsed"
    kinds = [
        str(item.get("kind"))
        for item in shape
        if isinstance(item, dict) and item.get("kind") is not None
    ]
    if len(kinds) == len(shape) and len(set(kinds)) == 1:
        return f"{kinds[0]}×{len(kinds)}"
    if (
        len(kinds) == len(shape)
        and len(kinds) % 2 == 0
        and all(kinds[i] == "tag" and kinds[i + 1] == "encode" for i in range(0, len(kinds), 2))
    ):
        return f"tag-encode×{len(kinds) // 2}"
    preview = "-".join(kinds[:8])
    if len(kinds) > 8:
        preview += f"+{len(kinds) - 8}"
    return preview or "unparsed"


def _camel_tokens(name: str) -> list[str]:
    core = name[:-2] if name.endswith("Up") else name
    return re.findall(r"[A-Z]+(?=[A-Z][a-z]|$)|[A-Z]?[a-z0-9]+", core)


def _clean_common_theme(names: list[str]) -> str | None:
    token_rows = [[t for t in _camel_tokens(name) if t not in _GENERIC_NAME_TOKENS] for name in names]
    token_rows = [row for row in token_rows if row]
    if len(token_rows) < 2:
        return None
    first = token_rows[0]
    best: list[str] = []
    for start in range(len(first)):
        for end in range(start + 1, len(first) + 1):
            candidate = first[start:end]
            if len(candidate) < len(best):
                continue
            found_everywhere = all(
                any(row[i:i + len(candidate)] == candidate for i in range(len(row) - len(candidate) + 1))
                for row in token_rows[1:]
            )
            if found_everywhere and len(candidate) > len(best):
                best = candidate
    if len(best) >= 2 or (best and len(best[0]) >= 6):
        return "".join(best)
    return None


def _shape_name_part(shape_summary: str) -> str:
    if re.fullmatch(r"tag-encode×\d+", shape_summary):
        return "Tuple"
    if re.fullmatch(r"encode×\d+", shape_summary):
        return "Sequence"
    if re.fullmatch(r"tag×\d+", shape_summary):
        return "TaggedFlow"
    return "EventFlow"


def _snake_case_name(name: str) -> str:
    core = name[:-2] if name.endswith("Up") else name
    parts = _camel_tokens(core)
    return "_".join(part.lower() for part in parts)


def _suggest_capstone_name(arity: int | None, shape_summary: str, names: list[str]) -> str:
    theme = _clean_common_theme(names)
    if theme:
        suggested = f"{theme}CarrierNameCertUp"
    else:
        arity_name = _ARITY_NAME.get(arity or 0, f"Arity{arity}" if arity else "Multi")
        suggested = f"BHist{arity_name}{_shape_name_part(shape_summary)}NameCertUp"
    return suggested if suggested.endswith("Up") else f"{suggested}Up"


def _capstone_candidate_dict(bucket: dict) -> dict:
    arity = bucket.get("arity")
    if not isinstance(arity, int):
        arity = None
    shape_summary = str(bucket.get("shape_summary") or "unparsed")
    members = bucket.get("members_sample", [])
    if not isinstance(members, list):
        members = []
    names = [str(name) for name in members if name]
    member_count = int(bucket.get("member_count") or len(names))
    suggested_lean_name = _suggest_capstone_name(arity, shape_summary, names)
    suggested_paper_slug = _snake_case_name(suggested_lean_name)
    return {
        "bucket_arity": arity,
        "bucket_shape": shape_summary,
        "bucket_member_count": member_count,
        "bucket_members_sample": names[:8],
        "suggested_lean_name": suggested_lean_name,
        "suggested_paper_slug": suggested_paper_slug,
        "suggested_paper_filename_prefix_hint": f"NNNN_{suggested_paper_slug}",
        "rationale": f"{member_count} chapters share a {shape_summary} BHist carrier event-flow pattern at arity {arity}.",
    }


def _capstone_candidate_sort_key(bucket: dict) -> tuple[int, int, str]:
    return (
        -int(bucket.get("member_count") or 0),
        int(bucket.get("arity") or 10**9),
        str(bucket.get("shape_summary") or ""),
    )


def _capstone_candidate_from_buckets(buckets: list[dict]) -> dict | None:
    valid = [
        bucket
        for bucket in buckets
        if isinstance(bucket, dict) and int(bucket.get("member_count") or 0) >= 2
    ]
    for bucket in sorted(valid, key=_capstone_candidate_sort_key):
        candidate = _capstone_candidate_dict(bucket)
        candidate_file = DERIVED_DIR / f"{candidate['suggested_lean_name']}.lean"
        if candidate_file.exists():
            continue
        return candidate
    return None


def _capstone_coverage_from_buckets(buckets: list[dict]) -> dict:
    covered_names = []
    total_phase2_buckets = 0
    for bucket in sorted(
        (bucket for bucket in buckets if isinstance(bucket, dict)),
        key=_capstone_candidate_sort_key,
    ):
        if int(bucket.get("member_count") or 0) < 2:
            continue
        total_phase2_buckets += 1
        candidate = _capstone_candidate_dict(bucket)
        suggested_lean_name = candidate["suggested_lean_name"]
        if (DERIVED_DIR / f"{suggested_lean_name}.lean").exists():
            covered_names.append(suggested_lean_name)
    covered = len(covered_names)
    return {
        "total_phase2_buckets": total_phase2_buckets,
        "covered": covered,
        "uncovered": total_phase2_buckets - covered,
        "covered_names": covered_names,
    }


def _get_carrier_isomorphism_summary() -> dict:
    """Return a small carrier-isomorphism summary, not the full audit JSON."""
    global _carrier_isomorphism_cache
    if _carrier_isomorphism_cache is not None:
        return _carrier_isomorphism_cache

    try:
        result = subprocess.run(
            ["python3", str(ROOT / "lean4" / "scripts" / "bedc_ci.py"),
             "carrier-isomorphism", "--json"],
            cwd=str(ROOT),
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except subprocess.TimeoutExpired:
        _carrier_isomorphism_cache = {
            "available": False,
            "reason": "carrier-isomorphism timed out after 30s",
        }
        return _carrier_isomorphism_cache
    except Exception as exc:
        _carrier_isomorphism_cache = {
            "available": False,
            "reason": f"carrier-isomorphism failed to start: {exc}",
        }
        return _carrier_isomorphism_cache

    if result.returncode != 0:
        stderr = (result.stderr or result.stdout or "").strip()
        _carrier_isomorphism_cache = {
            "available": False,
            "reason": stderr[:500] or f"carrier-isomorphism exited {result.returncode}",
        }
        return _carrier_isomorphism_cache

    try:
        payload = json.loads(result.stdout)
    except Exception as exc:
        _carrier_isomorphism_cache = {
            "available": False,
            "reason": f"carrier-isomorphism JSON parse failed: {exc}",
        }
        return _carrier_isomorphism_cache

    buckets = payload.get("phase2_buckets", [])
    if not isinstance(buckets, list):
        buckets = []
    ranked = sorted(
        enumerate(buckets, start=1),
        key=lambda item: len(item[1].get("members", [])) if isinstance(item[1], dict) else 0,
        reverse=True,
    )
    phase2_buckets = []
    for bucket_id, bucket in ranked:
        if not isinstance(bucket, dict):
            continue
        fingerprint = bucket.get("fingerprint", {})
        if not isinstance(fingerprint, dict):
            fingerprint = {}
        members = bucket.get("members", [])
        if not isinstance(members, list):
            members = []
        names = [
            str(member.get("name"))
            for member in members
            if isinstance(member, dict) and member.get("name")
        ]
        phase2_buckets.append({
            "bucket_id": bucket_id,
            "arity": fingerprint.get("arity"),
            "shape_summary": _shape_summary(fingerprint.get("shape")),
            "member_count": len(members),
            "members_sample": names[:8],
        })
    top_buckets = []
    for bucket in phase2_buckets[:10]:
        members_preview = list(bucket["members_sample"][:5])
        if bucket["member_count"] > 5:
            members_preview.append("...")
        top_buckets.append({
            "bucket_id": bucket["bucket_id"],
            "arity": bucket["arity"],
            "shape_summary": bucket["shape_summary"],
            "member_count": bucket["member_count"],
            "members_preview": members_preview,
        })

    _carrier_isomorphism_cache = {
        "available": True,
        "carriers_scanned": payload.get("carriers_scanned"),
        "phase2_buckets": phase2_buckets,
        "phase2_top_buckets": top_buckets,
    }
    return _carrier_isomorphism_cache


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
    import time as _time
    tmp_dir = Path(tempfile.gettempdir())
    head = _git_head_short()
    cache_path = tmp_dir / f"bedc_objective_grades_{head}.json"

    if cache_path.exists():
        try:
            data = json.loads(cache_path.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                _objective_grades_cache = data
                # Opportunistic LRU prune (cheap when under cap: only
                # glob + len-check). Runs on every critical_path call so
                # exact-HEAD cache hits also keep the temp dir bounded.
                _prune_objective_grades_cache_files(tmp_dir, keep=50)
                return data
        except Exception:
            pass

    STALE_CACHE_MAX_AGE_SECONDS = 6 * 3600  # 6h ceiling
    now = _time.time()
    stale_candidates = sorted(
        tmp_dir.glob("bedc_objective_grades_*.json"),
        key=lambda p: p.stat().st_mtime if p.exists() else 0,
        reverse=True,
    )
    for stale in stale_candidates:
        try:
            age = now - stale.stat().st_mtime
        except OSError:
            continue
        if age > STALE_CACHE_MAX_AGE_SECONDS:
            break  # everything older is even more stale
        try:
            data = json.loads(stale.read_text(encoding="utf-8"))
        except Exception:
            continue
        if not (isinstance(data, dict) and data):
            continue
        _objective_grades_cache = data
        try:
            cache_path.write_text(json.dumps(data), encoding="utf-8")
        except Exception:
            pass
        _prune_objective_grades_cache_files(tmp_dir, keep=50)
        return data

    AXIOM_PURITY_BUDGET_SECONDS = 300
    try:
        result = subprocess.run(
            ["python3", "lean4/scripts/bedc_ci.py",
             "axiom-purity", "--strict", "--json"],
            cwd=str(ROOT), capture_output=True, text=True, check=False,
            timeout=AXIOM_PURITY_BUDGET_SECONDS,
        )
        if result.returncode == 0 and result.stdout.strip():
            payload = json.loads(result.stdout)
            pure_set = set(payload.get("pure", []))
        else:
            pure_set = set()
    except (subprocess.TimeoutExpired, Exception):
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
    # Always persist — even an empty/partial result spares the next worker
    # from repeating the 5-min axiom-purity attempt under the same HEAD.
    try:
        cache_path.write_text(json.dumps(grades), encoding="utf-8")
    except Exception:
        pass
    _prune_objective_grades_cache_files(tmp_dir, keep=50)
    return grades


def _prune_objective_grades_cache_files(tmp_dir: Path, keep: int = 50) -> None:
    """LRU eviction for `bedc_objective_grades_<HEAD>.json` files.

    codex-auto-dev advances HEAD every 1-2 minutes; each new HEAD that
    misses the exact cache writes a fresh ~2.5MB file. Without eviction
    the temp dir accumulates GBs (observed 1299 files / 3.3GB) over a
    24h pipeline run. Keep the `keep` newest files (ample stale-fallback
    supply within the 6h window) and delete the rest. Best-effort:
    failures (e.g. file deleted by sibling worker between listdir and
    unlink) are silently ignored.
    """
    try:
        files = list(tmp_dir.glob("bedc_objective_grades_*.json"))
    except OSError:
        return
    if len(files) <= keep:
        return
    try:
        files.sort(key=lambda p: p.stat().st_mtime if p.exists() else 0,
                   reverse=True)
    except OSError:
        return
    for stale in files[keep:]:
        try:
            stale.unlink()
        except OSError:
            pass


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


# Per-call recursive-read memo: chapters are read by extract_horizons,
# compute_paper_priority_surfaces, is_chapter_retired_from_horizon (called
# from extract_horizons), _collect_siblings, and compute_root_unblocks —
# the same hub chapter can be recursive-read 3-5x per critical_path run.
# At ~2000 chapters with hub-only layout (each closure can pull in dozens
# of sibling .tex files totalling hundreds of KB), repeated full recursion
# becomes the dominant cost. Memoize by resolved path; the memo is reset
# at process start (module-level), so each fresh critical_path invocation
# pays the read cost once and amortizes across all callers.
_read_chapter_recursive_memo: dict[Path, str] = {}


def _read_chapter_recursive(chapter_path: Path,
                              seen: "set | None" = None) -> str:
    """Read a paper chapter and recursively follow `\\input{...}` includes.
    Returns the concatenated text. `seen` guards against include cycles.
    All `\\input` paths are resolved relative to PAPER_ROOT_DIR (matching
    pdflatex's working directory)."""
    if seen is None:
        seen = set()
    chapter_path = chapter_path.resolve()
    # Top-level memo hit: when called without an active include cycle
    # (seen is empty before adding this path), we can safely cache the
    # full closure result keyed on this path. Mid-recursion calls (seen
    # non-empty) cannot use the memo because the result would depend on
    # which ancestors are already in `seen`.
    can_memo = not seen
    if can_memo and chapter_path in _read_chapter_recursive_memo:
        return _read_chapter_recursive_memo[chapter_path]
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
    result = "".join(parts)
    if can_memo:
        _read_chapter_recursive_memo[chapter_path] = result
    return result


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
        try:
            text = tex.read_text(encoding="utf-8", errors="replace")
        except (FileNotFoundError, OSError):
            continue
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


def _has_human_derivation_gap(text: str) -> tuple[bool, list[str]]:
    if "\\origin{human}" not in text:
        return (False, [])
    notclaimed = " ".join(m.group(1) for m in NOTCLAIMED_RE.finditer(text))
    notclaimed_lower = notclaimed.lower()
    canonical_hits = [
        term for term in _HUMAN_CANONICAL_TERMS
        if term in notclaimed_lower
    ]
    if not canonical_hits:
        return (False, [])
    if _has_induction_proof(text):
        return (False, [])
    reasons = ["origin{human}", "canonical_notclaimed"]
    reasons.extend(f"notclaimed:{term.replace(' ', '_')}" for term in canonical_hits[:4])
    return (True, reasons)


def _is_metacic_priority(name: str, file_paper: str, text: str) -> tuple[bool, list[str]]:
    path_haystack = f"{name}\n{file_paper}"
    path_hit = METACIC_RE.search(path_haystack)
    import_hit = "BEDC.MetaCIC" in text
    if not path_hit and not import_hit:
        return (False, [])
    reasons = []
    if path_hit:
        reasons.append("metacic_path")
    if import_hit:
        reasons.append("imports_bedc_metacic")
    return (True, reasons)


def compute_paper_priority_surfaces(
    horizons: dict[str, dict],
    downstream: dict[str, int],
) -> dict[str, list[dict]]:
    human_rows: list[dict] = []
    metacic_rows: list[dict] = []
    for info in horizons.values():
        file_paper = info.get("file_paper")
        if not file_paper:
            continue
        tex = ROOT / file_paper
        text = _read_chapter_recursive(tex)
        name = str(info.get("name", ""))
        base = {
            "name": name,
            "file_paper": file_paper,
            "file_lean": info.get("file_lean"),
            "downstream": downstream.get(name, 0),
            "thms": info.get("thms", 0),
            "labels": info.get("labels", 0),
            "theory_grade": info.get("theory_grade"),
            "formal_grade": info.get("formal_grade"),
            "next_axis": info.get("next_axis"),
            "next_grade_transition": info.get("next_grade_transition"),
        }
        gap, gap_reasons = _has_human_derivation_gap(text)
        if gap:
            row = dict(base)
            row["score"] = downstream.get(name, 0) + max(1, info.get("labels", 0) - info.get("thms", 0))
            row["priority_signal"] = "human_derivation_gap"
            row["reasons"] = gap_reasons
            human_rows.append(row)
        metacic, metacic_reasons = _is_metacic_priority(name, file_paper, text)
        if metacic:
            row = dict(base)
            row["score"] = downstream.get(name, 0) + max(1, info.get("labels", 0))
            row["priority_signal"] = "metacic_priority"
            row["reasons"] = metacic_reasons
            metacic_rows.append(row)
    human_rows.sort(key=lambda r: (-r["score"], -r["labels"], r["file_paper"]))
    metacic_rows.sort(key=lambda r: (-r["score"], -r["labels"], r["file_paper"]))
    return {
        "human_derivation_gap": human_rows,
        "metacic_priority": metacic_rows,
    }


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


def compute_empty_roots(horizons: dict[str, dict],
                        downstream: dict[str, int],
                        *, recent_attack_threshold: int = 1) -> list[dict]:
    """Identify open chapters whose paper schema is fully empty
    (`max(thms, labels) == 0`) — i.e. root-of-tree stubs that no paper
    round has ever populated. These are the chapters that block the
    largest TRANSITIVE fan-outs from ever becoming `deps_ready`, and
    `compute_root_unblocks` cannot surface them when the dep tree has
    mutual-blocker structure (each root has multiple `thms=0` peers, so
    no root is a SINGLE-blocker for any downstream).

    Empirically (2026-05-08): when `top` collapses to 0, all 10 entries
    in `top_root_unblocks` have `unblock_count=1` because the bottom
    layer (affinespace, bilinform, chernweil, …) is mutually-blocking.
    The existing `unblock_count >= 3` GATE in phase_review.txt then
    skips, so paper rounds never attack these stubs and the pipeline
    stalls on closure-axis bookkeeping.

    `top_empty_roots` ranks by transitive_downstream (how many chapters
    transitively depend on this one) — directly measures "writing a
    schema here unblocks N downstream paths."

    Filters: open + not SCHEMA_ONLY + `max(thms, labels) == 0` + not
    in-flight + `recent_attacks < threshold` (30-min window, default 1).
    Sort: descending by `transitive_downstream`, then `direct_downstream`,
    then name.
    """
    recent = _recent_paper_attack_chapter_counts(window_minutes=30)
    inflight = _inflight_paper_attack_chapters()
    candidates: list[dict] = []
    # Compute direct downstream count (one hop) for tie-breaking.
    direct: dict[str, int] = {n: 0 for n in horizons}
    for n, info in horizons.items():
        for d in info.get("deps", []):
            if d in direct:
                direct[d] += 1
    for n, info in horizons.items():
        if info.get("closed"):
            continue
        if n in SCHEMA_ONLY_HORIZONS:
            continue
        thms = info.get("thms", 0) or 0
        labels = info.get("labels", 0) or 0
        if max(thms, labels) > 0:
            continue
        if n in inflight:
            continue
        recent_count = recent.get(n, 0)
        if recent_count >= recent_attack_threshold:
            continue
        candidates.append({
            "name": n,
            "thms": thms,
            "labels": labels,
            "deps": info.get("deps", []),
            "transitive_downstream": downstream.get(n, 0),
            "direct_downstream": direct.get(n, 0),
            "recent_attacks": recent_count,
            "file_paper": info.get("file_paper"),
        })
    candidates.sort(key=lambda r: (-r["transitive_downstream"],
                                    -r["direct_downstream"], r["name"]))
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


def compute_capstone_overlap_map() -> dict:
    """Build a discovery board of vision-to-vision shared coverage.

    For each pair (and triple) of vision chapters in
    `papers/bedc/parts/visions/`, compute the intersection of the
    Lean targets they cite via \\leanchecked, \\leanvariant,
    \\leandef, \\leanstmt, \\leansorryd, \\leantarget markers — and
    the kernel-object namespace prefixes those targets fall under.

    A pair (or triple) whose intersection is non-empty is an open
    vision slot unless a fourth vision already \\autorefs
    both/all sources and overlaps the shared targets — in which case
    the slot is marked unified_by that fourth capstone.

    This is a SOFT signal for paper P-rounds, not a HARD GATE.
    Discovery of non-trivial unifying structure is not mechanizable.
    """
    from itertools import combinations

    capstone_dir = ROOT / "papers/bedc/parts/visions"
    marker_re = re.compile(
        r"\\(?:leanchecked|leanvariant|leandef|leanstmt|leansorryd|leantarget)\{([^}]+)\}"
    )
    autoref_re = re.compile(
        r"\\autoref\{(?:ch|sec|thm|def|cor|rem|lem):visions-([a-zA-Z0-9_-]+)"
    )
    kernel_object_patterns = [
        (re.compile(r"(?:\\mathsf\{BHist\}|\\Hist\b|\bBHist\b|\\hsame\b|\bhsame\b)"),
         "BEDC.FKernel.Hist"),
        (re.compile(r"(?:\\mathsf\{BMark\}|\\Mark\b|\bBMark\b|\\msame\b|\bmsame\b)"),
         "BEDC.FKernel.Mark"),
        (re.compile(r"(?:\\Cont\b|\bCont\b)"), "BEDC.FKernel.Cont"),
        (re.compile(r"(?:\\Ext\b|\bExt\b)"), "BEDC.FKernel.Ext"),
        (re.compile(r"(?:\\NameCert\b|\bNameCert\b)"), "BEDC.FKernel.NameCert"),
    ]

    paths = [
        path for path in capstone_dir.glob("*.tex")
        if path.name not in {"index.tex", "_index_files.tex"}
    ]
    stems = sorted(path.stem for path in paths)
    stem_set = set(stems)
    records = {}

    for path in paths:
        text = path.read_text(encoding="utf-8", errors="replace")
        targets = {
            match.group(1).replace("\\_", "_")
            for match in marker_re.finditer(text)
        }
        prefixes = set()
        for target in targets:
            parts = target.split(".")
            if len(parts) >= 3 and target.startswith("BEDC."):
                prefixes.add(".".join(parts[:3]))
        for pattern, prefix in kernel_object_patterns:
            if pattern.search(text):
                prefixes.add(prefix)
        autorefs = {
            match.group(1).replace("-", "_")
            for match in autoref_re.finditer(text)
        }
        records[path.stem] = {
            "targets": targets,
            "prefixes": prefixes,
            "autorefs": autorefs & stem_set,
        }

    pairs_list = []
    for a, b in combinations(stems, 2):
        shared_targets = records[a]["targets"] & records[b]["targets"]
        shared_kernel_objects = records[a]["prefixes"] & records[b]["prefixes"]
        if not shared_kernel_objects:
            continue
        unified_by = None
        for c in stems:
            if c in {a, b}:
                continue
            if a not in records[c]["autorefs"] or b not in records[c]["autorefs"]:
                continue
            if shared_targets:
                coverage = len(records[c]["targets"] & shared_targets)
                if coverage < 0.5 * len(shared_targets):
                    continue
            unified_by = c
            break
        pairs_list.append({
            "a": a,
            "b": b,
            "shared_kernel_objects": sorted(shared_kernel_objects),
            "shared_lean_targets": sorted(shared_targets),
            "unified_by": unified_by,
            "a_autorefs_b": b in records[a]["autorefs"],
            "b_autorefs_a": a in records[b]["autorefs"],
        })

    triples_list = []
    for a, b, c in combinations(stems, 3):
        kernel_isect = (
            records[a]["prefixes"] & records[b]["prefixes"] & records[c]["prefixes"]
        )
        if not kernel_isect:
            continue
        target_isect = (
            records[a]["targets"] & records[b]["targets"] & records[c]["targets"]
        )
        unified_by = None
        for d in stems:
            if d in {a, b, c}:
                continue
            if (
                a in records[d]["autorefs"]
                and b in records[d]["autorefs"]
                and c in records[d]["autorefs"]
            ):
                unified_by = d
                break
        triples_list.append({
            "a": a,
            "b": b,
            "c": c,
            "shared_kernel_objects": sorted(kernel_isect),
            "shared_lean_targets": sorted(target_isect),
            "unified_by": unified_by,
        })

    pairs_list.sort(
        key=lambda item: (
            item["unified_by"] is not None,
            -len(item["shared_kernel_objects"]),
            -len(item["shared_lean_targets"]),
            item["a"],
            item["b"],
        )
    )
    triples_list.sort(
        key=lambda item: (
            item["unified_by"] is not None,
            -len(item["shared_kernel_objects"]),
            -len(item["shared_lean_targets"]),
            item["a"],
            item["b"],
            item["c"],
        )
    )

    return {
        "pairs": pairs_list,
        "triples": triples_list,
        "capstone_count": len(stems),
        "open_pairs_total": sum(1 for item in pairs_list if item["unified_by"] is None),
        "open_triples_total": sum(1 for item in triples_list if item["unified_by"] is None),
    }


# === Theorem-level discovery (D-1, additive — does not affect existing surfaces) ===
#
# Scans main.tex reverse-traversal closure for every \begin{theorem|lemma|...}
# environment, extracts (kind, label, file, line, nearby lean marker), classifies
# its zone by path prefix, and assigns an anchor_status. Used to build a
# `theorem_inventory` summary so workers can eventually consume a paper-wide
# unformalized theorem stream regardless of which zone (horizon / capstones /
# core / ground_compiler / proof_obligations / ...) the theorem lives in.

THEOREM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|definition|proposition|corollary)\}",
    re.MULTILINE,
)
LABEL_INSIDE_RE = re.compile(r"\\label\{((?:thm|def|lem|prop|cor):[^}]+)\}")
ALL_MARKERS_RE = re.compile(
    r"\\(leanchecked|leanvariant|leandef|leanstmt|leansorryd|leantarget)\{([^}]+)\}"
)
# Kernel objects already implemented in BEDC.FKernel.* — appearance in a
# theorem body marks it as "directly formalisable now", no new namespace needed.
KERNEL_OBJECT_RE = re.compile(
    r"\\(?:BHist|BMark|Cont|Ext|Mark|hsame|msame|Hist|Pkg|NameCert|Sig|Bundle|"
    r"Gap|Ask|InGap|InBundle|sameSig|psame|Settled|Unary|"
    r"DerivCert|ClosureCert|TheoryGate|FormalStatus)\b"
)
# Paper-wide cross-reference patterns. Both \autoref and \ref count toward
# downstream_refs (a label cited by N other places is N times more impactful
# to formalise — its anchor will be re-used).
AUTOREF_OR_REF_RE = re.compile(
    r"\\(?:autoref|ref|cref|Cref)\{((?:thm|def|lem|prop|cor):[^}]+)\}"
)

# Per-zone weight in unformalized_top score. Capstones get a >1 boost because
# each capstone bridge unifies ≥3 horizons, so its formalisation has supra-
# linear leverage; ground_compiler is < 1 to prevent its 995 unwritten from
# crowding the top 50 out, but kernel-grounded entries inside ground_compiler
# get their weight ×2 (handled in score formula). Zones not listed default to
# 0.4 (neither boosted nor crushed).
ZONE_WEIGHTS: dict[str, float] = {
    "horizon":                       1.0,
    "narrative.capstones":           1.2,
    "narrative.core":                0.8,
    "narrative.proof_obligations":   0.7,
    "narrative.proof_sprint":        0.6,
    "narrative.proof_standing":      0.6,
    "narrative.ground_compiler":     0.5,
    "narrative.formalization":       0.5,
    "narrative.hardening":           0.5,
    "narrative.concrete_hardening":  0.5,
    "narrative.acceptance":          0.3,
}

# Per-zone default Lean namespace prefix. None means the zone is intentionally
# never formalised (governance / frontmatter / appendices). Suggestions are a
# starting point for workers; workers may override.
ZONE_LEAN_PREFIX: dict[str, str | None] = {
    "horizon":                       "BEDC.Derived",
    "narrative.core":                "BEDC.FKernel",
    "narrative.ground_compiler":     "BEDC.Compiler",
    "narrative.capstones":           "BEDC.Capstones",
    "narrative.proof_obligations":   "BEDC.ProofObligation",
    "narrative.proof_sprint":        "BEDC.ProofSprint",
    "narrative.proof_standing":      "BEDC.ProofStanding",
    "narrative.formalization":       "BEDC.Formalization",
    "narrative.acceptance":          "BEDC.Acceptance",
    "narrative.hardening":           "BEDC.Hardening",
    "narrative.concrete_hardening":  "BEDC.ConcreteHardening",
    "narrative.project_governance":  None,
    "narrative.frontmatter":         None,
    "narrative.appendices":          None,
    "meta":                          None,
}


def _discover_paper_files() -> list[Path]:
    """main.tex \\input{} closure, recursively."""
    in_pdf: set[Path] = set()
    main = PAPER_ROOT_DIR / "main.tex"

    def follow(p: Path) -> None:
        p = p.resolve()
        if p in in_pdf or not p.exists():
            return
        in_pdf.add(p)
        try:
            text = p.read_text(encoding="utf-8", errors="replace")
        except Exception:
            return
        for m in INPUT_RE.finditer(text):
            rel = m.group(1).strip()
            if not rel.endswith(".tex"):
                rel = rel + ".tex"
            child = (PAPER_ROOT_DIR / rel).resolve()
            follow(child)

    follow(main)
    return sorted(in_pdf)


def _classify_zone(file_path: Path) -> str:
    """Path-prefix based zone. Returns 'horizon' / 'narrative.<dir>' / 'meta' / 'unknown'."""
    try:
        rel = file_path.relative_to(PAPER_ROOT_DIR.resolve())
    except ValueError:
        return "unknown"
    parts = rel.parts
    if parts and parts[0] in ("main.tex", "preamble.tex"):
        return "meta"
    if len(parts) >= 2 and parts[0] == "parts":
        zone_dir = parts[1]
        if zone_dir == "concrete_instances":
            return "horizon"
        return f"narrative.{zone_dir}"
    if len(parts) == 1 and parts[0].endswith(".tex"):
        # parts/<zone>.tex hub files (e.g. parts/core.tex)
        zone_dir = parts[0][:-4]
        if zone_dir == "concrete_instances":
            return "horizon"
        return f"narrative.{zone_dir}"
    return "unknown"


def _slug_to_camel(slug: str) -> str:
    """thm:nat-zero-classifier-uniqueness → NatZeroClassifierUniqueness."""
    if ":" in slug:
        slug = slug.split(":", 1)[1]
    parts = re.split(r"[-_]+", slug)
    return "".join(p[:1].upper() + p[1:] for p in parts if p)


def _infer_lean_anchor(file_path: Path, label: str | None,
                        zone: str) -> str | None:
    """Suggest a default BEDC namespace + identifier for a paper label.

    Returns None for zones not eligible for formalisation, or when label is
    missing. Result is a SUGGESTION — workers may override. Used so downstream
    surfaces can hint a Lean target name when paper writes \\begin{theorem}
    without a \\leanchecked / \\leandef marker.
    """
    prefix = ZONE_LEAN_PREFIX.get(zone)
    if prefix is None or not label:
        return None
    try:
        rel = file_path.relative_to(PAPER_ROOT_DIR.resolve())
    except ValueError:
        return None
    parts = rel.parts
    suffix = _slug_to_camel(label)

    if zone == "horizon":
        m = re.match(r"\d+_([a-z][a-z0-9_]*?)_namecert", parts[-1])
        if m:
            chapter = m.group(1)
            return f"{prefix}.{chapter[:1].upper()}{chapter[1:]}Up.{suffix}"
        # sub-dir sibling: parts/concrete_instances/<theme>/<sib>.tex
        if len(parts) >= 4 and parts[1] == "concrete_instances":
            chapter = parts[2]
            return f"{prefix}.{chapter[:1].upper()}{chapter[1:]}Up.{suffix}"
        return f"{prefix}.{suffix}"

    if zone.startswith("narrative."):
        chapter_stem = parts[-1].replace(".tex", "")
        # Strip leading numeric prefix (00_ / 14_ / 256_ etc.)
        chapter_stem = re.sub(r"^\d+[a-z]?_", "", chapter_stem)
        sub = _slug_to_camel(chapter_stem)
        if sub:
            return f"{prefix}.{sub}.{suffix}"
        return f"{prefix}.{suffix}"

    return None


def _load_theorem_envs_cache() -> dict:
    try:
        if not _THEOREM_ENVS_CACHE_PATH.exists():
            return {}
        data = json.loads(_THEOREM_ENVS_CACHE_PATH.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _save_theorem_envs_cache(cache: dict) -> None:
    try:
        tmp = _THEOREM_ENVS_CACHE_PATH.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(cache, ensure_ascii=False), encoding="utf-8")
        tmp.replace(_THEOREM_ENVS_CACHE_PATH)
    except Exception:
        pass


def _load_lean_decls_cache() -> dict:
    try:
        if not _LEAN_DECLS_CACHE_PATH.exists():
            return {}
        data = json.loads(_LEAN_DECLS_CACHE_PATH.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def _save_lean_decls_cache(cache: dict) -> None:
    try:
        tmp = _LEAN_DECLS_CACHE_PATH.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(cache, ensure_ascii=False), encoding="utf-8")
        tmp.replace(_LEAN_DECLS_CACHE_PATH)
    except Exception:
        pass


def _build_declared_set() -> set[str]:
    """Per-file cached set of qualified Lean names declared in lean4/BEDC/."""
    try:
        sys_path_addition = str((ROOT / "lean4" / "scripts").resolve())
        import sys as _sys
        if sys_path_addition not in _sys.path:
            _sys.path.insert(0, sys_path_addition)
        from bedc_ci import collect_declarations, lean_files  # type: ignore
    except Exception:
        return set()

    cache = _load_lean_decls_cache() if _CACHE_ENABLED else {}
    new_cache: dict = {}
    declared: set[str] = set()

    for path in lean_files():
        try:
            file_rel = str(path.relative_to(ROOT))
        except ValueError:
            file_rel = str(path)
        try:
            mtime = path.stat().st_mtime
        except Exception:
            continue

        cached_entry = cache.get(file_rel) if isinstance(cache, dict) else None
        if (
            isinstance(cached_entry, dict)
            and cached_entry.get("mtime") == mtime
            and isinstance(cached_entry.get("decls"), list)
        ):
            decls_list = cached_entry["decls"]
        else:
            try:
                file_decls, _file_fields = collect_declarations(path)
                decls_list = [d.qualified_name for d in file_decls]
            except Exception:
                decls_list = []

        new_cache[file_rel] = {"mtime": mtime, "decls": decls_list}
        for q in decls_list:
            declared.add(str(q))

    if _CACHE_ENABLED:
        _save_lean_decls_cache(new_cache)
    return declared


def _count_paper_wide_autorefs(files: list[Path]) -> dict[str, int]:
    """Count how many times each \\label is cited via \\autoref / \\ref / \\cref
    across all .tex files reachable from main.tex. Returns {label: count}.
    Used to compute downstream_refs for the unformalized_top score: a theorem
    cited by N other places is N× more impactful to formalise."""
    counts: dict[str, int] = {}
    for f in files:
        try:
            text = f.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        for m in AUTOREF_OR_REF_RE.finditer(text):
            label = m.group(1)
            counts[label] = counts.get(label, 0) + 1
    return counts


def _scan_theorem_envs_for_file(text: str) -> list[dict]:
    envs: list[dict] = []
    line_starts = [0] + [i + 1 for i, c in enumerate(text) if c == "\n"]
    for m in THEOREM_ENV_RE.finditer(text):
        kind = m.group(1)
        start = m.start()
        line_start = bisect.bisect_right(line_starts, start)
        window = text[start:start + 4000]
        label_m = LABEL_INSIDE_RE.search(window)
        label = label_m.group(1) if label_m else None
        marker_m = ALL_MARKERS_RE.search(window)
        actual_anchor = (
            marker_m.group(2).replace("\\_", "_").strip()
            if marker_m else None
        )
        marker_kind = marker_m.group(1) if marker_m else None

        body_window = window[:1200]
        statement_preview = re.sub(r"\s+", " ", body_window).strip()[:200]
        has_kernel = bool(KERNEL_OBJECT_RE.search(body_window))

        envs.append({
            "kind": kind,
            "line": line_start,
            "label": label,
            "anchor_actual": actual_anchor,
            "marker_kind": marker_kind,
            "statement_preview": statement_preview,
            "has_kernel_object": has_kernel,
        })
    return envs


def discover_all_theorems() -> list[dict]:
    """Scan paper-wide tree (from main.tex) for every theorem environment.

    For each \\begin{theorem|lemma|definition|proposition|corollary} env, look
    forward up to 4000 chars for a \\label{} and any \\leanchecked/\\leandef/
    etc. marker. Classify zone by file path prefix. Compute anchor_status:
      - one of objective FORMAL_GRADE_ORDER tokens if marker target exists
      - 'stale'      if marker target exists in source but not declared in build
      - 'unwritten'  if no marker present

    Each row also carries:
      - statement_preview (first 200 chars of body, newlines collapsed)
      - has_kernel_object (body mentions \\BHist / \\NameCert / etc — already
                           formalised, can attack now without new namespace)
      - downstream_refs   (paper-wide \\autoref / \\ref / \\cref count)
      - zone_weight       (per-zone multiplier in score)
      - score             (downstream_refs * zone_weight; ground_compiler
                           kernel-grounded gets weight ×2)
    """
    files = _discover_paper_files()
    objective_grades = load_objective_formal_grades()
    declared_set = _build_declared_set()
    autoref_counts = _count_paper_wide_autorefs(files)
    cache = _load_theorem_envs_cache() if _CACHE_ENABLED else {}
    new_cache: dict = {}

    rows: list[dict] = []
    for f in files:
        zone = _classify_zone(f)
        if zone in ("unknown", "meta"):
            continue
        try:
            mtime = f.stat().st_mtime
        except Exception:
            continue
        try:
            file_rel = str(f.relative_to(ROOT))
        except ValueError:
            file_rel = str(f)
        cached_entry = cache.get(file_rel)
        if (
            isinstance(cached_entry, dict)
            and cached_entry.get("mtime") == mtime
            and isinstance(cached_entry.get("envs"), list)
        ):
            envs = cached_entry["envs"]
        else:
            try:
                text = f.read_text(encoding="utf-8", errors="replace")
            except Exception:
                continue
            envs = _scan_theorem_envs_for_file(text)
        if _CACHE_ENABLED:
            new_cache[file_rel] = {"mtime": mtime, "envs": envs}
        # Chapter inference for grouping: the namecert hub name when in horizon,
        # otherwise the file stem stripped of leading numeric prefix.
        try:
            rel = f.relative_to(PAPER_ROOT_DIR.resolve())
            parts = rel.parts
        except ValueError:
            parts = ()
        if zone == "horizon" and parts:
            m_chap = re.match(r"\d+_([a-z][a-z0-9_]*?)_namecert", parts[-1])
            if m_chap:
                chapter = m_chap.group(1)
            elif len(parts) >= 4 and parts[1] == "concrete_instances":
                chapter = parts[2]
            else:
                chapter = parts[-1].replace(".tex", "")
        elif parts:
            stem = parts[-1].replace(".tex", "")
            chapter = re.sub(r"^\d+[a-z]?_", "", stem)
        else:
            chapter = None

        for env in envs:
            if not isinstance(env, dict):
                continue
            kind = env.get("kind")
            line_start = env.get("line")
            label = env.get("label")
            actual_anchor = env.get("anchor_actual")
            marker_kind = env.get("marker_kind")
            if actual_anchor:
                # Skip placeholder targets like `BEDC.<...>.<theorem>` —
                # paper uses `<...>` as template syntax in didactic
                # examples (e.g. acceptance/01_derivation_acceptance_gate),
                # not as a real Lean target. They're not drift.
                if "<" in actual_anchor and ">" in actual_anchor:
                    anchor_status = "placeholder"
                elif actual_anchor in declared_set:
                    grade = objective_grades.get(actual_anchor, "encodedDefV")
                    anchor_status = grade
                else:
                    anchor_status = "stale"
                suggested = None
            else:
                anchor_status = "unwritten"
                suggested = _infer_lean_anchor(f, label, zone)

            statement_preview = env.get("statement_preview")
            has_kernel = bool(env.get("has_kernel_object"))

            # Score formula: paper-wide cross-reference count, weighted by
            # zone. ground_compiler kernel-grounded entries get a ×2 boost so
            # the ~101 "attackable now" theorems can rise above the ~894
            # "needs new namespace" peers within the same zone.
            base_weight = ZONE_WEIGHTS.get(zone, 0.4)
            if zone == "narrative.ground_compiler" and has_kernel:
                weight = base_weight * 2.0
            else:
                weight = base_weight
            downstream = autoref_counts.get(label or "", 0)
            score = downstream * weight

            rows.append({
                "id": label or f"unlabeled:{f.name}:{line_start}",
                "kind": kind,
                "file": file_rel,
                "line": line_start,
                "zone": zone,
                "chapter": chapter,
                "label": label,
                "anchor_actual": actual_anchor,
                "anchor_suggested": suggested,
                "marker_kind": marker_kind,
                "anchor_status": anchor_status,
                "statement_preview": statement_preview,
                "has_kernel_object": has_kernel,
                "downstream_refs": downstream,
                "zone_weight": round(weight, 2),
                "score": round(score, 2),
            })
    if _CACHE_ENABLED:
        _save_theorem_envs_cache(new_cache)
    return rows


def compute_unformalized_top(rows: list[dict], max_n: int = 50) -> list[dict]:
    """Rank unwritten theorems paper-wide by score desc, return top max_n.
    Strips per-row fields not useful at the top level (chapter / id stay)."""
    candidates = [r for r in rows if r["anchor_status"] == "unwritten"]
    candidates.sort(key=lambda r: (
        -r["score"], -r["downstream_refs"], r["zone"], r["file"], r["line"]
    ))
    out = []
    for r in candidates[:max_n]:
        out.append({
            "id": r["id"],
            "kind": r["kind"],
            "file": r["file"],
            "line": r["line"],
            "zone": r["zone"],
            "chapter": r["chapter"],
            "label": r["label"],
            "anchor_suggested": r["anchor_suggested"],
            "statement_preview": r["statement_preview"],
            "has_kernel_object": r["has_kernel_object"],
            "downstream_refs": r["downstream_refs"],
            "zone_weight": r["zone_weight"],
            "score": r["score"],
        })
    return out


def compute_drift_top(rows: list[dict], max_n: int = 50) -> list[dict]:
    """Theorems whose paper-side \\leanchecked/\\leandef target does not
    resolve to a declared Lean identifier (rename / move / typo). Each is a
    1-line fix: edit the marker to point at the current canonical name. Sort
    by downstream_refs desc — fix the most-cited drift first."""
    candidates = [r for r in rows if r["anchor_status"] == "stale"]
    candidates.sort(key=lambda r: (-r["downstream_refs"], r["file"], r["line"]))
    out = []
    for r in candidates[:max_n]:
        out.append({
            "id": r["id"],
            "kind": r["kind"],
            "file": r["file"],
            "line": r["line"],
            "zone": r["zone"],
            "chapter": r["chapter"],
            "label": r["label"],
            "anchor_actual": r["anchor_actual"],   # what paper currently writes
            "marker_kind": r["marker_kind"],
            "statement_preview": r["statement_preview"],
            "downstream_refs": r["downstream_refs"],
        })
    return out


def summarize_theorem_inventory(rows: list[dict]) -> dict:
    """Aggregate a theorem-list into headline counters for baseline reporting."""
    from collections import Counter
    by_zone = Counter(r["zone"] for r in rows)
    by_anchor = Counter(r["anchor_status"] for r in rows)
    by_kind = Counter(r["kind"] for r in rows)
    by_chapter = Counter((r["zone"], r["chapter"]) for r in rows if r["chapter"])
    # Per-zone unwritten count (the ground-truth "what's left to formalise"
    # surface, broken down by zone — D-1 baseline metric).
    by_zone_unwritten = Counter(
        r["zone"] for r in rows if r["anchor_status"] == "unwritten"
    )
    return {
        "total": len(rows),
        "by_kind": dict(by_kind.most_common()),
        "by_zone": dict(by_zone.most_common()),
        "by_anchor_status": dict(by_anchor.most_common()),
        "by_zone_unwritten": dict(by_zone_unwritten.most_common()),
        "top_chapters_by_density": [
            {"zone": z, "chapter": c, "count": n}
            for (z, c), n in by_chapter.most_common(20)
        ],
    }


def main(argv: list[str] | None = None) -> int:
    global _CACHE_ENABLED
    parser = argparse.ArgumentParser(
        description="发现 BEDC critical-path 派发候选。"
    )
    parser.add_argument(
        "--no-cache",
        action="store_true",
        help="绕过 theorem-env 与 declared-set 缓存。",
    )
    args = parser.parse_args(argv)
    _CACHE_ENABLED = not args.no_cache

    horizons = extract_horizons()
    downstream = transitive_downstream(horizons)

    # Read the strict threshold from .pipeline_parallel.json (default 5).
    strict = read_deps_ready_threshold()
    paper_priority_config = read_paper_priority_config()

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
    empty_roots = compute_empty_roots(horizons, downstream)
    paper_priority = compute_paper_priority_surfaces(horizons, downstream)

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
    # Same lesson as bridge_sync_pending: do NOT inflight-filter
    # bridge_candidates. With ~40 mature/axiomClean chapters and
    # 12+ concurrent lean rounds, the filter empties the surface
    # within one dispatch wave; the lean orchestrator then sees
    # surface=[], runs phase B with empty top, and emits
    # `{"targets": []}` triggering cooldown. Letting in-flight
    # chapters stay in surface lets the merge-time dedup handle
    # rate limiting naturally and keeps lean rounds productive.
    inflight_lean = _inflight_lean_attack_chapters()  # used by formal_axis_top below
    bridge_candidates_full.sort(key=lambda c: c.get("thms", 0), reverse=True)
    # Per-call shuffle to disperse 12-worker dogpile.
    import random as _rand_bc
    _surface_bc = bridge_candidates_full[:10]
    _rand_bc.Random().shuffle(_surface_bc)
    bridge_candidates = _surface_bc

    # NOTE: do NOT inflight-filter bridge_sync_pending. With only ~5
    # candidates total, the inflight filter empties the surface within
    # one round-dispatch wave; new rounds then see surface=[] but
    # codex remembers <X>Up_StdBridge by self-grep and re-proposes
    # CommRingUp / AddUp / FieldUp from memory, dedup drops, no
    # progress. Allowing in-flight chapters into the surface lets new
    # rounds pick the same chapter as a sibling and the merge layer's
    # dedup correctly drops one of the duplicates after the first
    # successful merge — natural rate limiting, not lock-out.
    bridge_sync_pending_full.sort(key=lambda c: c.get("thms", 0), reverse=True)
    # Per-call shuffle stays — disperses 10-worker simultaneous
    # selection of the same top-1 across the candidate set.
    _surface_bsp = bridge_sync_pending_full[:10]
    import random as _rand2
    _rand2.Random().shuffle(_surface_bsp)
    bridge_sync_pending = _surface_bsp

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
        "paper_priority_mode": paper_priority_config["paper_priority_mode"],
        "paper_priority_strength": paper_priority_config["paper_priority_strength"],
        "closed_horizons": closed_count,
        "open_horizons": open_count,
        "human_derivation_gap_total": len(paper_priority["human_derivation_gap"]),
        "metacic_priority_total": len(paper_priority["metacic_priority"]),
        "human_derivation_gap": paper_priority["human_derivation_gap"][:25],
        "metacic_priority": paper_priority["metacic_priority"][:25],
        "drift_chapters_total": len(drift_chapters_full),
        "bridge_candidates_total": len(bridge_candidates_full),
        "bridge_sync_pending_total": len(bridge_sync_pending_full),
        "bridge_sync_pending": bridge_sync_pending,
        "formal_axis_top_total": len(formal_axis_top_full),
        "granularity": "sibling",
        "top": rolled[:25],
        "top_root_unblocks": root_unblocks[:10],
        "top_empty_roots_total": len(empty_roots),
        "top_empty_roots": empty_roots[:10],
        "top_transitions": top_transitions,
        "drift_chapters": drift_chapters,
        "bridge_candidates": bridge_candidates,
        "formal_axis_top": formal_axis_top,
        "capstone_overlap_map": compute_capstone_overlap_map(),
        "carrier_isomorphism": _get_carrier_isomorphism_summary(),
    }
    # Theorem-level surfaces (D-1 inventory + D-2 unformalized_top / drift_top).
    # Compute discover_all_theorems() once and reuse — the scan is the heaviest
    # call in the whole script (touches ~1100 .tex files paper-wide).
    theorem_rows = discover_all_theorems()
    payload["theorem_inventory"] = summarize_theorem_inventory(theorem_rows)
    payload["unformalized_top"] = compute_unformalized_top(theorem_rows, max_n=50)
    payload["drift_top"] = compute_drift_top(theorem_rows, max_n=50)
    # Compute dispatch weights inline for prompt consumption.
    try:
        carrier = payload.get("carrier_isomorphism", {})
        if isinstance(carrier, dict) and carrier.get("available"):
            candidate_buckets = carrier.get("phase2_buckets", [])
            if isinstance(candidate_buckets, list):
                capstone_coverage = _capstone_coverage_from_buckets(candidate_buckets)
                carrier_iso_phase2_bucket_count = capstone_coverage["uncovered"]
                capstone_candidate = _capstone_candidate_from_buckets(candidate_buckets)
            else:
                carrier_iso_phase2_bucket_count = 0
                capstone_candidate = None
                capstone_coverage = None
        else:
            carrier_iso_phase2_bucket_count = 0
            capstone_candidate = None
            capstone_coverage = None
        supply_lean = {
            "top": len(rolled),
            "formal_axis_top": len(formal_axis_top_full),
            "unformalized_top": len(payload.get("unformalized_top", [])),
            "carrier_isomorphism_capstone": carrier_iso_phase2_bucket_count,
        }
        supply_paper = {
            "top": len(rolled),
            "top_root_unblocks": len(root_unblocks),
            "closure_mark": _count_closure_mark_candidates(),
            "carrier_isomorphism_capstone": carrier_iso_phase2_bucket_count,
            "human_derivation_gap": len(paper_priority["human_derivation_gap"]),
            "metacic_priority": len(paper_priority["metacic_priority"]),
        }
        consumption = _compute_consumption_60min()
        payload["dispatch_weights"] = _compute_dispatch_weights(
            supply_lean, supply_paper, consumption,
            _LEAN_BASE_WEIGHTS, _PAPER_BASE_WEIGHTS,
            capstone_candidate, capstone_coverage,
            paper_priority_config,
        )
    except Exception as exc:
        payload["dispatch_weights"] = {"error": str(exc)[:200]}
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
