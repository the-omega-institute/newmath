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
        [--gate register-only|vocab|math|oversized|leanvariant|all]

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
    r"(?<!\\)\\\[",
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


def _load_lint_patterns() -> dict:
    """Read LINT_PATTERNS_FILE if present; else fall back to in-script
    defaults. Recompiled on every call — this script is short-lived
    (one round invocation) so caching has no benefit."""
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
    if not base_sha:
        return []
    out = _git(
        ["diff", "--unified=0", f"{base_sha}..HEAD", "--", rel_path],
        cwd=worktree,
    )
    rows: list[tuple[int, str]] = []
    hunk_re = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")
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


GATE_DISPATCH = {
    "register-only": detect_register_only,
    "vocab": detect_vocab,
    "math": detect_math,
    "oversized": detect_oversized,
    "leanvariant": detect_leanvariant,
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
