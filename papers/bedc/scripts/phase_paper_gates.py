#!/usr/bin/env python3
"""Pre-merge content lint gates for paper rounds.

Runs in the worktree after rebase, before merge, on the diff
`<base-branch>..HEAD` under `papers/bedc/`. Each gate scans added
lines and/or whole changed files and emits violations.

Used by `codex_revise.py::verify_worktree_commits` via subprocess.
Splitting the gates into their own script means the patterns and
gate logic can be tightened or relaxed without restarting the
orchestrator — the next round's pre-merge call re-loads them.

Usage:

    python3 papers/bedc/scripts/phase_paper_gates.py \\
        --worktree /path/to/round_P1234 \\
        --base-sha abc123                     \\
        [--gate register-only|vocab|math|oversized|leanvariant|axis-confusion|all]

With `--gate all` (default), prints a JSON object keyed by gate name.
With a specific gate name, prints one violation per line.

Exit code is always 0 unless infrastructure (subprocess, JSON parse)
breaks. The orchestrator decides which gates block the round and
which are advisory.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable

SCRIPT_DIR = Path(__file__).resolve().parent
LINT_PATTERNS_FILE = SCRIPT_DIR / "lint_patterns.json"

MAX_TEX_FILE_LINES = 800

_DEFAULT_FORBIDDEN_VOCAB = [
    "新增", "新版", "修订", "修复了上一版本",
    "增量", "修改记录", "变更记录", "变更原因",
    "patch", "migration", "frozen", "supersede", "superseded",
    "deprecated", "legacy", "increment",
    "rectification", "amendment",
]
_DEFAULT_FORBIDDEN_VERSION_PATTERN = (
    r"\bv\d+\.\d+\.[Xx0-9]+\b|\bv\d+-[A-Za-z0-9_-]+"
)
_DEFAULT_FORBIDDEN_MATH_PATTERNS = [
    r"\\begin\{equation\*?\}",
    r"\\begin\{align\*?\}",
    r"\\begin\{eqnarray\*?\}",
]

LEAN_MARKER_RE = re.compile(
    r"\\(leanchecked|leanvariant|leanstmt|leandef|leansorryd)\{([^}]+)\}"
)


def _build_vocab_regex(words: list[str]) -> re.Pattern:
    """ASCII tokens get `\\b...\\b` word boundaries so 'patch' does not
    match inside 'dispatch'. CJK words match as-is (Python's `\\b` is
    too narrow for CJK)."""
    parts: list[str] = []
    for w in words:
        esc = re.escape(w)
        if w.isascii():
            parts.append(rf"\b{esc}\b")
        else:
            parts.append(esc)
    return re.compile(r"(" + "|".join(parts) + r")", re.IGNORECASE)


def _ensure_lint_patterns_file() -> None:
    """Self-bootstrap: copy `lint_patterns.json.template` over to
    `lint_patterns.json` if the latter is missing. Idempotent."""
    if LINT_PATTERNS_FILE.exists():
        return
    template = LINT_PATTERNS_FILE.with_suffix(LINT_PATTERNS_FILE.suffix + ".template")
    if template.exists():
        try:
            LINT_PATTERNS_FILE.write_text(template.read_text(encoding="utf-8"),
                                          encoding="utf-8")
        except Exception:
            pass


def _load_lint_patterns() -> dict:
    """Read LINT_PATTERNS_FILE if present; else fall back to in-script
    defaults. Recompiled on every call — this script is short-lived
    (one round invocation) so caching has no benefit."""
    _ensure_lint_patterns_file()
    try:
        if LINT_PATTERNS_FILE.exists():
            data = json.loads(LINT_PATTERNS_FILE.read_text(encoding="utf-8"))
            vocab = data.get("forbidden_vocab", _DEFAULT_FORBIDDEN_VOCAB)
            version = data.get(
                "forbidden_version_pattern", _DEFAULT_FORBIDDEN_VERSION_PATTERN
            )
            math = data.get(
                "forbidden_math_patterns", _DEFAULT_FORBIDDEN_MATH_PATTERNS
            )
        else:
            vocab = _DEFAULT_FORBIDDEN_VOCAB
            version = _DEFAULT_FORBIDDEN_VERSION_PATTERN
            math = _DEFAULT_FORBIDDEN_MATH_PATTERNS
    except Exception:
        vocab = _DEFAULT_FORBIDDEN_VOCAB
        version = _DEFAULT_FORBIDDEN_VERSION_PATTERN
        math = _DEFAULT_FORBIDDEN_MATH_PATTERNS
    return {
        "vocab": _build_vocab_regex(vocab),
        "version": re.compile(version),
        "math": re.compile(r"(" + "|".join(math) + r")"),
    }


def _git(args: list[str], *, cwd: Path) -> str:
    try:
        r = subprocess.run(
            ["git", *args], cwd=str(cwd),
            capture_output=True, text=True, timeout=60,
        )
        return r.stdout or ""
    except Exception:
        return ""


def _changed_files(*, worktree: Path, base_sha: str,
                   prefix: str = "", diff_filter: str = "AM") -> list[str]:
    if not base_sha:
        return []
    out = _git(
        ["diff", "--name-only", f"--diff-filter={diff_filter}",
         f"{base_sha}..HEAD", "--", prefix or "."],
        cwd=worktree,
    )
    return [l.strip() for l in out.splitlines() if l.strip()]


def _changed_tex_files(*, worktree: Path, base_sha: str) -> list[str]:
    return [
        f for f in _changed_files(
            worktree=worktree, base_sha=base_sha, prefix="papers/bedc/"
        )
        if f.endswith(".tex")
    ]


def _added_lines_per_file(*, worktree: Path, base_sha: str,
                          rel_path: str) -> list[tuple[int, str]]:
    """Return (line_no, content) tuples for lines this round added.

    A round's own additions are the union of added lines across the
    round's NON-MERGE commits between `base_sha` and `HEAD`. Merge
    commits (which import sibling P-rounds' work and the BASE branch
    sync) are excluded; lines they bring in are NOT this round's
    responsibility — they belong to the round that originally wrote
    them and were already gated at that round's verify step.

    Also filters by `--diff-filter=AM`: only files added or modified
    in the round's own commit set are scanned.
    """
    if not base_sha:
        return []
    # List the round's own (non-merge) commits oldest-first.
    log_out = _git(
        ["log", "--no-merges", "--reverse", "--pretty=%H",
         f"{base_sha}..HEAD"],
        cwd=worktree,
    )
    own_commits = [c.strip() for c in log_out.splitlines() if c.strip()]
    if not own_commits:
        return []
    rows: list[tuple[int, str]] = []
    hunk_re = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")
    for sha in own_commits:
        out = _git(
            ["diff", "--unified=0", f"{sha}^!", "--", rel_path],
            cwd=worktree,
        )
        current_new: int | None = None
        for line in out.splitlines():
            m = hunk_re.match(line)
            if m:
                current_new = int(m.group(1))
                continue
            if current_new is None:
                continue
            if line.startswith("+") and not line.startswith("+++"):
                rows.append((current_new, line[1:]))
                current_new += 1
            elif line.startswith("-") and not line.startswith("---"):
                pass
            else:
                current_new += 1
    return rows


def detect_register_only(*, worktree: Path, base_sha: str) -> list[str]:
    tex = _changed_tex_files(worktree=worktree, base_sha=base_sha)
    lean = [
        f for f in _changed_files(worktree=worktree, base_sha=base_sha)
        if f.startswith("lean4/")
    ]
    if not tex and not lean:
        return ["no .tex or .lean files changed in this round"]
    if tex and not lean:
        all_added: list[str] = []
        for rel in tex:
            for _, content in _added_lines_per_file(
                worktree=worktree, base_sha=base_sha, rel_path=rel
            ):
                if content.strip():
                    all_added.append(content.strip())
        if all_added and all(
            LEAN_MARKER_RE.search(line) and "leanvariant" in line
            for line in all_added
        ):
            return ["round only adds new \\leanvariant markers; not allowed"]
    return []


def detect_vocab(*, worktree: Path, base_sha: str) -> list[str]:
    pats = _load_lint_patterns()
    vocab_re = pats["vocab"]
    version_re = pats["version"]
    violations: list[str] = []
    for rel in _changed_files(
        worktree=worktree, base_sha=base_sha, prefix="papers/bedc/"
    ):
        if not (rel.endswith(".tex") or rel.endswith(".md")):
            continue
        for line_no, content in _added_lines_per_file(
            worktree=worktree, base_sha=base_sha, rel_path=rel
        ):
            stripped = content.strip()
            for m in vocab_re.finditer(stripped):
                violations.append(
                    f"{rel}:{line_no}: '{m.group(1)}' — {stripped[:120]}"
                )
                break
            else:
                vm = version_re.search(stripped)
                if vm:
                    violations.append(
                        f"{rel}:{line_no}: version-prefix "
                        f"'{vm.group(0)}' — {stripped[:120]}"
                    )
    return violations


def detect_math(*, worktree: Path, base_sha: str) -> list[str]:
    math_re = _load_lint_patterns()["math"]
    violations: list[str] = []
    for rel in _changed_tex_files(worktree=worktree, base_sha=base_sha):
        for line_no, content in _added_lines_per_file(
            worktree=worktree, base_sha=base_sha, rel_path=rel
        ):
            m = math_re.search(content)
            if m:
                violations.append(
                    f"{rel}:{line_no}: forbidden math env "
                    f"'{m.group(1)}' — {content.strip()[:120]}"
                )
    return violations


def detect_oversized(*, worktree: Path, base_sha: str) -> list[str]:
    violations: list[str] = []
    for rel in _changed_tex_files(worktree=worktree, base_sha=base_sha):
        try:
            n = len((worktree / rel).read_text(encoding="utf-8").splitlines())
        except Exception:
            continue
        if n > MAX_TEX_FILE_LINES:
            violations.append(
                f"{rel}: {n} lines exceeds cap {MAX_TEX_FILE_LINES}"
            )
    return violations


def detect_leanvariant(*, worktree: Path, base_sha: str) -> list[str]:
    violations: list[str] = []
    for rel in _changed_tex_files(worktree=worktree, base_sha=base_sha):
        for line_no, content in _added_lines_per_file(
            worktree=worktree, base_sha=base_sha, rel_path=rel
        ):
            for m in LEAN_MARKER_RE.finditer(content):
                if m.group(1) == "leanvariant":
                    violations.append(
                        f"{rel}:{line_no}: new \\leanvariant{{{m.group(2)}}}"
                    )
    return violations


AXIS_CONFUSION_PHRASES = (
    re.compile(
        r"theory(?:\s+is)?\s+closed\s+because\s+(?:it\s+is\s+|the\s+)?(?:lean|machine|formal)",
        re.I,
    ),
    re.compile(
        r"unchecked,?\s+therefore\s+not\s+closed",
        re.I,
    ),
    re.compile(
        r"\\theoryclosure\{[^}]*\}\s*=>?\s*\\formalstatus",
    ),
    re.compile(
        r"\\formalstatus\{[^}]*\}\s*=>?\s*\\theoryclosure",
    ),
)


_SIBLING_REF_RE = re.compile(
    r"\\autoref\{ch:concrete-instances-([a-z][a-z0-9\-]*?)(?:-namecert)?\}"
)
_VISION_REF_RE = re.compile(
    r"\\autoref\{ch:visions-([a-z][a-z0-9\-]*?)\}"
)
# Catch-all: any `\autoref{ch:<slug>}` referencing a chapter that is NOT the
# own chapter (vision chapters historically use `ch:<slug>` not
# `ch:visions-<slug>`, so the strict patterns above miss legitimate
# cross-references). The orphan check accepts a match here as a valid
# sibling/anchor reference.
_GENERIC_CH_REF_RE = re.compile(
    r"\\autoref\{ch:([a-z][a-z0-9\-]*)\}"
)
# Capture the full label tail (greedy). Self-ref classification is done by
# walking the dashed parts and joining prefixes; the lazy regex used before
# matched just the first character as the slug, causing every self-ref to
# look like a cross-ref. See `_label_is_self_ref` below.
_LABEL_RE = re.compile(
    r"\\autoref\{(?:thm|def|lem|cor|prop)[A-Za-z]*:([a-z][a-z0-9\-]*)\}"
)
# Allow underscores AND digits in slug (e.g.
# `3939_metacic_subject_reduction_obstruction_namecert_construction.tex` was
# silently skipped by the underscore-free regex, letting orphan chapters
# slip past the gate).
_NAMECERT_FILE_RE = re.compile(
    r"^papers/bedc/parts/concrete_instances/(?:[^/]+/)?"
    r"\d+_([a-z][a-z0-9_]*?)_namecert_construction\.tex$"
)


def _label_is_self_ref(label_tail: str, own_slug_compact: str) -> bool:
    """Decide whether `label_tail` (dashed, e.g. "subject-reduction-discharge-carrier")
    starts with this chapter's own slug.

    `own_slug_compact` is the filename slug with underscores stripped (e.g.
    "subjectreductiondischarge" from a filename of
    `..._subject_reduction_discharge_namecert_construction.tex` or
    `..._subjectreductiondischarge_namecert_construction.tex`). We split the
    dashed label into parts and try every prefix concatenation against the
    compact slug — if any prefix concat equals own_slug, the label resolves
    to this chapter and counts as a self-ref.
    """
    parts = label_tail.split("-")
    for i in range(len(parts), 0, -1):
        if "".join(parts[:i]) == own_slug_compact:
            return True
    return False


def detect_orphan_new_chapter(*, worktree: Path, base_sha: str) -> list[str]:
    """Reject newly-added concrete-instances NameCert chapters that contain
    zero cross-references to a sibling chapter or vision chapter.

    Background: by 2026-05-13 the dossier dependency graph showed 447 of 652
    concrete-instances chapters with zero `\\autoref{ch:...}` cross-refs —
    every newly-generated chapter was a kernel-only float, citing only its
    own `\\autoref{thm:<self-slug>-...}` labels. The pipeline accumulated a
    star-graph fan-out from kernel instead of a horizontal lattice between
    domains.

    A new chapter must show how its content RELATES to existing chapters:
    either via an explicit `\\autoref{ch:concrete-instances-<sibling>-namecert}`
    macro, an `\\autoref{ch:visions-<vision>}` anchor back to the originating
    vision narrative, OR a forward `\\autoref{thm:<sibling-slug>-...}` /
    `\\autoref{def:<sibling-slug>-...}` cite that resolves to a different
    sibling slug. Self-refs (slug == own slug) do not count.
    """
    if not base_sha:
        return []
    # Added (not modified) NameCert chapters in this round
    added = _changed_files(
        worktree=worktree, base_sha=base_sha,
        prefix="papers/bedc/parts/concrete_instances/", diff_filter="A",
    )
    added = [p for p in added if p.endswith(".tex")]
    if not added:
        return []

    violations: list[str] = []
    for rel in added:
        m = _NAMECERT_FILE_RE.match(rel)
        if not m:
            # `*_namecert_construction.tex` is the canonical pattern; other
            # patterns (sub-files for one chapter) are not anchor chapters
            # and are not gated here.
            continue
        # Slug from filename — may contain underscores; compact form is
        # the underscore-stripped lowercase identifier used to match the
        # dashed label prefixes via `_label_is_self_ref`.
        own_slug_compact = m.group(1).replace("_", "")
        path = worktree / rel
        if not path.exists():
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue

        sibling_refs: set[str] = set()
        for slug in _SIBLING_REF_RE.findall(text):
            slug_norm = slug.replace("-", "")
            if slug_norm and slug_norm != own_slug_compact:
                sibling_refs.add(slug_norm)
        vision_refs = {v for v in _VISION_REF_RE.findall(text)}
        thm_def_refs: set[str] = set()
        for label_tail in _LABEL_RE.findall(text):
            if not _label_is_self_ref(label_tail, own_slug_compact):
                thm_def_refs.add(label_tail)
        # Generic chapter cross-refs: accept any `\autoref{ch:X}` where X is
        # not the own chapter slug. Covers vision chapters labeled as
        # `\label{ch:<slug>}` (legacy style without `visions-` prefix).
        generic_ch_refs: set[str] = set()
        for slug in _GENERIC_CH_REF_RE.findall(text):
            slug_norm = slug.replace("-", "").replace("_", "")
            # exclude self-ref (own_slug_compact already drops underscores)
            if slug_norm and own_slug_compact not in slug_norm and slug_norm not in own_slug_compact:
                generic_ch_refs.add(slug_norm)

        if not (sibling_refs or vision_refs or thm_def_refs or generic_ch_refs):
            violations.append(
                f"{rel}: ORPHAN — new NameCert chapter has zero cross-references "
                f"to a sibling concrete-instances chapter or vision chapter. "
                f"Required: at least one `\\autoref{{ch:concrete-instances-"
                f"<sibling>-namecert}}` (or `\\autoref{{ch:visions-<slug>}}` "
                f"if vision-anchored, or `\\autoref{{thm:<sibling>-...}}` / "
                f"`\\autoref{{def:<sibling>-...}}` resolving to a different "
                f"slug than `{own_slug_compact}`). Self-refs do not count."
            )
    return violations


_ORIGIN_AI_RE = re.compile(r"\\origin\{ai\}")
_FIELD_FAITHFUL_INSTANCE_RE = re.compile(
    r"\binstance\s+\w+FieldFaithful\s*:?\s*FieldFaithful\s+\w+Up\b"
)


def detect_ai_chapter_missing_field_faithful(*, worktree: Path, base_sha: str) -> list[str]:
    """Reject FIRST-PROPOSAL `\\origin{ai}` chapter commits whose Lean-side
    `TasteGate.lean` does not contain a `FieldFaithful <X>Up` instance.

    "First proposal" means EITHER the .tex file is newly added in this
    round, OR this round's diff added a `\\origin{ai}` line (transition
    from `\\origin{human}` or no origin marker). Maintenance edits on
    chapters that were ALREADY `\\origin{ai}` in `base_sha` are exempt —
    the FF backfill is R-side responsibility tracked via critical_path,
    not a per-P-commit gate (the old behavior retroactively penalized
    chapters predating the 2026-05-13 TasteGate stage C upgrade).

    Background: TasteGate `round_trip` + `layer_separation` forces
    injectivity on inhabitants but not field-level faithfulness — a
    chapter with `XUp.mk a b c ... i` (9 BHist fields) could pass those
    gates while `toEventFlow` only encodes 2 of the 9 fields.
    `FieldFaithful` closes that loophole. `\\origin{human}` chapters
    are exempt entirely.
    """
    if not base_sha:
        return []
    # New or modified concrete_instances NameCert chapters in this round
    changed = _changed_files(
        worktree=worktree, base_sha=base_sha,
        prefix="papers/bedc/parts/concrete_instances/",
    )
    changed = [p for p in changed if p.endswith(".tex")]
    if not changed:
        return []

    # First-proposal classifier: union of (a) newly-added .tex files and
    # (b) files where `\origin{ai}` is present in HEAD but was NOT in
    # the base_sha version (genuine human→ai or none→ai transition).
    # Do NOT use `_added_lines_per_file` here: a file rewrite shows every
    # existing line as both deleted+added, which would mis-classify
    # routine maintenance commits as first-proposal.
    added_files = set(_changed_files(
        worktree=worktree, base_sha=base_sha,
        prefix="papers/bedc/parts/concrete_instances/",
        diff_filter="A",
    ))
    first_proposal: set[str] = set(added_files)
    for rel in changed:
        if rel in first_proposal:
            continue
        # File existed in base_sha. Check if `\origin{ai}` was already
        # present there. If yes → maintenance. If no → transition.
        try:
            base_text = _git(
                ["show", f"{base_sha}:{rel}"], cwd=worktree
            )
        except Exception:
            base_text = ""
        if _ORIGIN_AI_RE.search(base_text):
            continue  # already ai in base — maintenance edit
        first_proposal.add(rel)

    violations: list[str] = []
    for rel in changed:
        m = _NAMECERT_FILE_RE.match(rel)
        if not m:
            continue
        own_slug = m.group(1).replace("_", "")
        path = worktree / rel
        if not path.exists():
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if not _ORIGIN_AI_RE.search(text):
            continue  # `\origin{human}` or no origin — exempt

        if rel not in first_proposal:
            # Maintenance edit on chapter that was already `\origin{ai}`
            # before this round. FF backfill is R-side responsibility,
            # tracked via critical_path FF-gap signal; not a per-commit
            # gate. This prevents retroactive penalty on chapters
            # predating the 2026-05-13 TasteGate stage C upgrade.
            continue

        # Locate the chapter's TasteGate.lean. Convention: PascalCase the
        # compact slug then append `Up/TasteGate.lean`. e.g.
        # `dyadicprecision` → `DyadicPrecisionUp/TasteGate.lean`. Walk
        # the BEDC/Derived/ tree case-insensitively to find a folder
        # whose lowercase name matches `<own_slug>up`.
        derived_root = worktree / "lean4" / "BEDC" / "Derived"
        if not derived_root.exists():
            # Tree not present in this worktree's view — skip gate.
            continue
        target_folder = None
        target_token = own_slug + "up"
        for child in derived_root.iterdir():
            if child.is_dir() and child.name.lower() == target_token:
                target_folder = child
                break
        if target_folder is None:
            # First-proposal AI chapter without Lean scaffold — violation.
            # (We already filtered out maintenance edits above, so reaching
            # here means rel is a first-proposal.)
            violations.append(
                f"{rel}: ORIGIN-AI MISSING FIELDFAITHFUL — newly-added "
                f"\\origin{{ai}} chapter has no `lean4/BEDC/Derived/"
                f"<X>Up/TasteGate.lean` folder; the FieldFaithful "
                f"instance must be created alongside the paper chapter."
            )
            continue

        taste_file = target_folder / "TasteGate.lean"
        has_ff_instance = False
        if taste_file.exists():
            try:
                taste_text = taste_file.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                taste_text = ""
            if _FIELD_FAITHFUL_INSTANCE_RE.search(taste_text):
                has_ff_instance = True
        # Also accept the instance elsewhere in the chapter's folder
        if not has_ff_instance:
            for lean_file in target_folder.rglob("*.lean"):
                try:
                    body = lean_file.read_text(encoding="utf-8", errors="ignore")
                except OSError:
                    continue
                if _FIELD_FAITHFUL_INSTANCE_RE.search(body):
                    has_ff_instance = True
                    break

        if not has_ff_instance:
            violations.append(
                f"{rel}: ORIGIN-AI MISSING FIELDFAITHFUL — `\\origin{{ai}}` "
                f"chapter has no `instance ... : FieldFaithful <X>Up` in "
                f"`lean4/BEDC/Derived/{target_folder.name}/`. Add the "
                f"instance to TasteGate.lean per phase_c.txt §FieldFaithful."
            )
    return violations


_FALSIFIABLE_PRED_RE = re.compile(r"\\falsifiablePrediction\{")
_INDEPENDENCE_WITNESS_RE = re.compile(r"\\independenceWitness\{")


def detect_ai_chapter_missing_falsifiable_prediction(
    *, worktree: Path, base_sha: str
) -> list[str]:
    """Newly-added `\\origin{ai}` chapters MUST include one
    `\\falsifiablePrediction{...}` row stating a BEDC-verifiable
    consequence that, if disproved within N rounds, invalidates the
    chapter. Without this row, the chapter is not committing to any
    refutable claim and is therefore a vacuous placeholder."""
    if not base_sha:
        return []
    added = _changed_files(
        worktree=worktree, base_sha=base_sha,
        prefix="papers/bedc/parts/concrete_instances/", diff_filter="A",
    )
    added = [p for p in added if p.endswith(".tex")]
    violations: list[str] = []
    for rel in added:
        m = _NAMECERT_FILE_RE.match(rel)
        if not m:
            continue
        path = worktree / rel
        if not path.exists():
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if not _ORIGIN_AI_RE.search(text):
            continue  # human chapter — exempt
        if not _FALSIFIABLE_PRED_RE.search(text):
            violations.append(
                f"{rel}: AI MISSING FALSIFIABLE — `\\origin{{ai}}` "
                f"chapter has no `\\falsifiablePrediction{{...}}` row. "
                f"Every AI chapter must commit one BEDC-verifiable "
                f"consequence that, if disproved within N rounds, "
                f"invalidates the chapter (see preamble.tex / phase_c.txt)."
            )
    return violations


def detect_ai_chapter_missing_independence_witness(
    *, worktree: Path, base_sha: str
) -> list[str]:
    """Newly-added `\\origin{ai}` chapters claiming structural atomicity
    (i.e. NOT marked `\\origin{ai-composite}`) MUST include one
    `\\independenceWitness{...}` row naming 3-5 nearest siblings and
    explaining why the carrier is not bijective to any of them. This
    is the BEDC analogue of "this number is prime, not a product of
    smaller numbers". A chapter that cannot name siblings or justify
    independence is presumptively derivative."""
    if not base_sha:
        return []
    added = _changed_files(
        worktree=worktree, base_sha=base_sha,
        prefix="papers/bedc/parts/concrete_instances/", diff_filter="A",
    )
    added = [p for p in added if p.endswith(".tex")]
    violations: list[str] = []
    for rel in added:
        m = _NAMECERT_FILE_RE.match(rel)
        if not m:
            continue
        path = worktree / rel
        if not path.exists():
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        # Only enforce on bare \origin{ai}, not the composite variant.
        if not _ORIGIN_AI_RE.search(text):
            continue
        if re.search(r"\\origin\{ai-composite\}", text):
            continue  # composite chapters opt out
        if not _INDEPENDENCE_WITNESS_RE.search(text):
            violations.append(
                f"{rel}: AI MISSING INDEPENDENCE — `\\origin{{ai}}` "
                f"chapter has no `\\independenceWitness{{...}}` row. "
                f"Name 3-5 nearest sibling chapter slugs and explain "
                f"why the carrier is not bijective to any of them. "
                f"Compositional chapters should use `\\origin{{ai-composite}}` "
                f"instead to opt out of this gate."
            )
    return violations


def detect_axis_confusion(*, worktree: Path, base_sha: str) -> list[str]:
    violations: list[str] = []
    for rel in _changed_tex_files(worktree=worktree, base_sha=base_sha):
        for line_no, content in _added_lines_per_file(
            worktree=worktree, base_sha=base_sha, rel_path=rel
        ):
            for pat in AXIS_CONFUSION_PHRASES:
                if pat.search(content):
                    violations.append(
                        f"{rel}:{line_no}: closure/verification axis "
                        f"confusion — {content.strip()[:120]}"
                    )
                    break
    return violations


GATE_DISPATCH = {
    "register-only": detect_register_only,
    "vocab": detect_vocab,
    "math": detect_math,
    "oversized": detect_oversized,
    "leanvariant": detect_leanvariant,
    "axis-confusion": detect_axis_confusion,
    "orphan-new-chapter": detect_orphan_new_chapter,
    # FieldFaithful is a Lean-side instance; checking it from P is a layer
    # violation. R phase_c.txt enforces the FF HARD GATE on its own side
    # when formalizing `\origin{ai}` chapters. If R cannot satisfy FF,
    # R revises (carrier design, or relabels chapter origin) — not P.
    # "ai-missing-fieldfaithful": detect_ai_chapter_missing_field_faithful,
    "ai-missing-falsifiable": detect_ai_chapter_missing_falsifiable_prediction,
    "ai-missing-independence": detect_ai_chapter_missing_independence_witness,
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--worktree", type=Path, required=True)
    ap.add_argument("--base-sha", required=True,
                    help="commit SHA the round was based on (HEAD before round)")
    ap.add_argument("--gate", default="all",
                    choices=list(GATE_DISPATCH.keys()) + ["all"])
    args = ap.parse_args()

    wt = args.worktree
    base = args.base_sha
    if not wt.exists():
        print(f"phase_paper_gates: worktree {wt} does not exist",
              file=sys.stderr)
        return 2

    if args.gate == "all":
        results = {
            name: fn(worktree=wt, base_sha=base)
            for name, fn in GATE_DISPATCH.items()
        }
        print(json.dumps(results, ensure_ascii=False))
    else:
        for v in GATE_DISPATCH[args.gate](worktree=wt, base_sha=base):
            print(v)
    return 0


if __name__ == "__main__":
    sys.exit(main())
