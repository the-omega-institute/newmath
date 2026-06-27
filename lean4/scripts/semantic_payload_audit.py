#!/usr/bin/env python3
"""Full-tree semantic-payload audit for BEDC Derived theorems.

Refines the misleading raw `grep '(x : forall...hsame)'` count (which counts
every legitimate hsame-stability hypothesis) into the *conclusion-aware*
parameter-echo count, by reusing the exact predicate phase_d_lint already
applies to round diffs — only here it scans the whole BEDC/Derived tree.

This is the measurement harness the math-quality consensus asked for: turn the
2001 smoke-alarm into the real echo number, and locate where it concentrates.

Informational (always exit 0). os.walk (not rglob) so a worker removing a dir
mid-iteration cannot crash a long-running caller.
"""
import json
import os
import re
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
# When landed under lean4/scripts/ this import is a sibling; from scratchpad we
# add the real scripts dir so phase_d_lint's regexes stay the single source.
for cand in (SCRIPTS, "/Users/chronoai/newmath/lean4/scripts"):
    if cand not in sys.path:
        sys.path.insert(0, cand)

from phase_d_lint import (  # noqa: E402  reuse — do not duplicate the predicate
    PARAMETER_ECHO_BIND_RE,
    PARAMETER_ECHO_CONCL_RE,
    MECHANICAL_ARITY_RE,
    BHIST_CONSTRUCTOR_RE,
    _strip_hsame_tokens,
    _extract_conclusion,
)

DERIVED = "/Users/chronoai/newmath/lean4/BEDC/Derived"
HEAD_RE = re.compile(
    r"^[ \t]*(theorem|lemma|def|instance|structure|class|inductive|abbrev)[ \t]+([A-Za-z0-9_'.]+)",
    re.M,
)


def iter_blocks(text):
    """Yield (kind, name, block) for each top-level declaration in a file."""
    heads = list(HEAD_RE.finditer(text))
    for i, m in enumerate(heads):
        end = heads[i + 1].start() if i + 1 < len(heads) else len(text)
        yield m.group(1), m.group(2), text[m.start():end]


def is_param_echo(block):
    """Exact replica of phase_d_lint main-loop echo predicate (lines 307-318)."""
    sig = block.split(":=")[0]
    if not PARAMETER_ECHO_BIND_RE.search(sig):
        return False
    conclusion = _extract_conclusion(sig)
    if not PARAMETER_ECHO_CONCL_RE.search(conclusion):
        return False
    return not BHIST_CONSTRUCTOR_RE.search(_strip_hsame_tokens(conclusion))


def main():
    total_thm = 0
    raw_hsame_hyp = 0          # theorems whose signature binds a forall...hsame hyp
    real_echo = 0              # conclusion-aware parameter-echo (the true subset)
    arity = 0                  # mechanical-arity-named theorems
    no_anchor = 0              # derived theorem with no BEDC kernel anchor in block
    per_file_echo = {}
    echo_names = []
    for root, _dirs, files in os.walk(DERIVED, onerror=lambda e: None):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(root, fn)
            try:
                text = open(path, encoding="utf-8").read()
            except OSError:
                continue
            rel = os.path.relpath(path, DERIVED)
            for kind, name, block in iter_blocks(text):
                if kind not in ("theorem", "lemma"):
                    continue
                total_thm += 1
                if MECHANICAL_ARITY_RE.search(name):
                    arity += 1
                sig = block.split(":=")[0]
                if PARAMETER_ECHO_BIND_RE.search(sig):
                    raw_hsame_hyp += 1
                if is_param_echo(block):
                    real_echo += 1
                    per_file_echo[rel] = per_file_echo.get(rel, 0) + 1
                    if len(echo_names) < 40:
                        echo_names.append(f"{rel}::{name}")
                if not BHIST_CONSTRUCTOR_RE.search(block):
                    no_anchor += 1
    top_files = sorted(per_file_echo.items(), key=lambda kv: -kv[1])[:15]
    out = {
        "scope": "lean4/BEDC/Derived (theorem+lemma)",
        "total_theorems": total_thm,
        "raw_hsame_hyp_bind": raw_hsame_hyp,
        "real_param_echo_conclusion_aware": real_echo,
        "real_echo_pct_of_theorems": round(100 * real_echo / max(total_thm, 1), 2),
        "mechanical_arity_named": arity,
        "derived_thm_without_kernel_anchor": no_anchor,
        "top_echo_files": top_files,
        "sample_echo_names": echo_names,
        "_notes": {
            "real_param_echo_conclusion_aware": (
                "The trustworthy echo metric: hyp binds (x:forall...hsame) AND "
                "conclusion is forall...hsame AND no BEDC anchor survives the "
                "hsame/BHist strip. Reuses phase_d_lint's exact predicate. The raw "
                "`grep '(x:forall...hsame)'` line count overcounts ~400x because it "
                "matches legitimate hsame-stability hypotheses and non-theorem bodies."
            ),
            "derived_thm_without_kernel_anchor": (
                "WEAK signal, do not gate on it tree-wide: counts theorems whose "
                "block names no base-kernel token, but that legitimately includes "
                "higher-level derived math (octonion, Stern-Brocot, located reals) "
                "built on chapter-local carriers. Phase D's anchor check is a gate "
                "for NEW decls only, where the round context disambiguates."
            ),
        },
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
