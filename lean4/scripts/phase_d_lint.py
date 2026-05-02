#!/usr/bin/env python3
"""Phase D mechanical post-rebase lints for Lean rounds.

Runs after lake build / check-axioms / audit / axiom-purity, before merge.
Three checks on declarations introduced in this round
(`<base-branch>..HEAD` under `lean4/BEDC/`):

  1. Mechanical-arity suffix on a new declaration name
     (`_two`, `_three`, `_four`, `_five`, `_six`, `_*_step`,
     `_*_witness_chain`).
  2. Parameter-echo schema: signature binds a hypothesis
     `(name : forall … hsame …)` — i.e. quantifies over an hsame law as
     input rather than proving anything specific about a concrete BEDC
     kernel object.
  3. BHist-anchor: every new theorem under `BEDC.Derived.*` must mention
     at least one concrete BEDC kernel symbol in its signature
     (BHist / BMark / hsame / ProbeBundle / SigRel / NameCert / Pkg /
     etc).

Used by `codex_formalize.py::run_phase_d_lints` via subprocess. Splitting
the lint into its own script means the regex set can be tightened
without restarting the pipeline — the next call (next round's pre-merge
gate) picks up the change.

Usage:

    python3 lean4/scripts/phase_d_lint.py \
        --worktree /path/to/round_R1234 \
        --base-branch codex-auto-dev

Exit code 0 = clean. Exit code 1 = at least one violation; details on
stdout suitable for inclusion in a codex recovery prompt.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

DECL_RE = re.compile(
    r"^\s*(theorem|lemma|def|inductive|structure|class)\s+(\w+)"
)
MECHANICAL_ARITY_RE = re.compile(
    r"_(two|three|four|five|six)(?:_step)?(?:_witness_chain)?\b"
)
PARAMETER_ECHO_BIND_RE = re.compile(
    r"\(\s*(\w+)\s*:\s*(?:∀|forall)\b[^)]*hsame\b", re.DOTALL
)
PARAMETER_ECHO_CONCL_RE = re.compile(
    r"(?:∀|forall)\b[^,]*,[^.]*hsame\b", re.DOTALL
)


def _strip_hsame_tokens(text: str) -> str:
    """Drop `hsame` and the bare `BHist` type token so the residual anchor
    scan only fires on substantive constructors (Empty/e0/e1/Cont/NameCert/…)."""
    text = re.sub(r"\bhsame\b", "", text)
    text = re.sub(r"\bBHist\b", "", text)
    return text


def _extract_conclusion(sig: str) -> str:
    """Return the part of `sig` after the last top-level `:` (the goal type)."""
    depth = 0
    last_colon = -1
    for i, ch in enumerate(sig):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif ch == ":" and depth == 0:
            last_colon = i
    return sig[last_colon + 1:] if last_colon >= 0 else sig
BHIST_CONSTRUCTOR_RE = re.compile(
    r"\b("
    r"BHist|BMark|Empty|e0|e1|cons|append|sameSig|"
    r"ProbeBundle|SigRel|InGap|NameCert|SemanticNameCert|Pkg|hsame|msame|"
    r"Cont|Ext|InBundle|SameSig|UnaryHistory|StageInterface|"
    r"SealEvent|SealInterface|AskEvent|AskPolicy|BundleAskPolicy|"
    r"DescentCertificate|StableTransformation|ThreadFamily|"
    r"bundleAppend|bundleLength|bwordLength"
    r")\b"
)
DERIVED_PATH_PREFIX = "lean4/BEDC/Derived"
SIGNATURE_BLOCK_LIMIT = 40


def diff_added_decls(worktree: Path, base_branch: str) -> list[tuple[str, str]]:
    """Return [(name, signature_block)] for theorem/lemma/def added in
    this worktree relative to base_branch, scoped to lean4/BEDC/."""
    res = subprocess.run(
        [
            "git", "log", "-p", "--no-color", "--reverse",
            f"{base_branch}..HEAD", "--", "lean4/BEDC/",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    text = res.stdout or ""
    out: list[tuple[str, str]] = []
    pending: list[str] = []
    pending_name: str | None = None
    for raw in text.splitlines():
        if not raw.startswith("+") or raw.startswith("+++"):
            if pending_name is not None and pending:
                out.append((pending_name, "\n".join(pending)))
                pending_name = None
                pending = []
            continue
        line = raw[1:]
        m = DECL_RE.match(line)
        if m:
            if pending_name is not None and pending:
                out.append((pending_name, "\n".join(pending)))
            pending_name = m.group(2)
            pending = [line]
        elif pending_name is not None:
            pending.append(line)
            if len(pending) > SIGNATURE_BLOCK_LIMIT:
                out.append((pending_name, "\n".join(pending)))
                pending_name = None
                pending = []
    if pending_name is not None and pending:
        out.append((pending_name, "\n".join(pending)))
    return out


def declaration_in_derived(worktree: Path, name: str) -> bool:
    res = subprocess.run(
        ["git", "grep", "-l", "-F", f"theorem {name}", "--", DERIVED_PATH_PREFIX],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    return bool(res.stdout.strip())


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--worktree", type=Path, required=True)
    p.add_argument("--base-branch", type=str, required=True)
    args = p.parse_args()

    decls = diff_added_decls(args.worktree, args.base_branch)
    if not decls:
        return 0

    arity_hits: list[str] = []
    echo_hits: list[str] = []
    anchor_hits: list[str] = []
    for name, body in decls:
        if MECHANICAL_ARITY_RE.search(name):
            arity_hits.append(name)
            continue
        sig = body.split(":=")[0]
        is_derived = declaration_in_derived(args.worktree, name)
        if PARAMETER_ECHO_BIND_RE.search(sig):
            conclusion = _extract_conclusion(sig)
            if PARAMETER_ECHO_CONCL_RE.search(conclusion):
                concl_no_hsame = _strip_hsame_tokens(conclusion)
                if not BHIST_CONSTRUCTOR_RE.search(concl_no_hsame):
                    echo_hits.append(name)
        if is_derived and not BHIST_CONSTRUCTOR_RE.search(sig):
            anchor_hits.append(name)

    if not (arity_hits or echo_hits or anchor_hits):
        return 0

    msgs: list[str] = []
    if arity_hits:
        msgs.append(
            "Mechanical arity suffix on new declaration(s) (NAMING.md §3 forbids"
            " _two/_three/_four/_five/_six/_*_step/_*_witness_chain): "
            + ", ".join(arity_hits[:5])
        )
    if echo_hits:
        msgs.append(
            "Parameter-echo schema: signature binds (name : forall … hsame …) "
            "without anchoring on a concrete BEDC kernel object: "
            + ", ".join(echo_hits[:5])
        )
    if anchor_hits:
        msgs.append(
            "Derived theorem missing a BHist / BMark / hsame / ProbeBundle / "
            "SigRel / NameCert anchor in its signature: "
            + ", ".join(anchor_hits[:5])
        )
    print("\n".join(msgs))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
