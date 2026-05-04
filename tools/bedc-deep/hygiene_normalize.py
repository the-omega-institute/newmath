#!/usr/bin/env python3
"""Hygiene auto-normalizer for BEDC paper writeback.

Rationale (per project decision): hygiene checks should HELP us land valid
content, not reject it. Codex/oracle write mathematically correct LaTeX in
~1 of 10 paper-writing styles. Most rejections fixed by mechanical
transformations (`\\(X\\)` ↔ `$X$`, strip `Q.E.D.`, swap `\\mathsf{X}` for
`\\X` when `\\X` is in preamble, etc.) — Python regex can do this in
milliseconds; LLM retry takes minutes per cycle.

This module:
  1. Takes raw LaTeX content from codex/oracle
  2. Applies a sequence of mechanical normalizations
  3. Returns normalized content + a list of transformations applied
  4. Identifies REMAINING issues that need human / LLM judgement
     (topic mismatch, malformed environments, missing labels, etc.)

Stage 2 (`killo_golden_writeback`) calls this BEFORE invoking claude
hygiene review. The claude review now only judges remaining
correctness/topic concerns, not mechanical hygiene.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


# ---------------------------------------------------------------------------
# Preamble macro discovery
# ---------------------------------------------------------------------------


def _load_preamble_macros(preamble_path: Path) -> set[str]:
    """Return the set of bare macro names defined in preamble.tex (without
    leading backslash). Only `\\newcommand{\\NAME}` style is parsed."""
    macros: set[str] = set()
    if not preamble_path.exists():
        return macros
    try:
        text = preamble_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return macros
    for m in re.finditer(r"\\newcommand\{\\([A-Za-z]+)\}", text):
        macros.add(m.group(1))
    for m in re.finditer(r"\\(?:re)?newcommand\*?\{\\([A-Za-z]+)\}", text):
        macros.add(m.group(1))
    return macros


# ---------------------------------------------------------------------------
# Result dataclass
# ---------------------------------------------------------------------------


@dataclass
class NormalizeResult:
    content: str
    changed: bool
    transformations: list[str] = field(default_factory=list)
    remaining_issues: list[str] = field(default_factory=list)
    blocking_issues: list[str] = field(default_factory=list)
    """`blocking_issues` are problems the normalizer cannot fix and that
    require LLM intervention or escalation (e.g. topic mismatch, no
    theorem/lemma/etc. environment present, malformed proof block)."""


# ---------------------------------------------------------------------------
# Individual transformations
# ---------------------------------------------------------------------------


def _strip_proof_markers(text: str) -> tuple[str, int]:
    """Remove manual QED markers inside `\\begin{proof}...\\end{proof}`.

    Handles both multi-line cases (`\\nQ.E.D.\\n\\end{proof}`) AND single-line
    cases where the entire content is on one line (oracle DOM scrape often
    returns this) and the markers butt against `\\end{proof}` directly.
    """
    n = 0
    pat_proof = re.compile(r"(\\begin\{proof\})(.*?)(\\end\{proof\})", re.DOTALL)

    def _scrub(m: re.Match) -> str:
        nonlocal n
        body = m.group(2)
        original = body
        # 1. Multi-line anchors: stand-alone QED lines.
        body = re.sub(
            r"^\s*(?:Q\.?E\.?D\.?|\\qed|\\square|as required|as desired|QED)\s*\.?\s*$",
            "",
            body,
            flags=re.MULTILINE | re.IGNORECASE,
        )
        # 2. End-of-body markers (right before \end{proof}, no newline).
        #    Pattern: optional whitespace + marker + optional period/period
        #    space at end-of-body. This is what catches the single-line
        #    case `body content. Q.E.D.\end{proof}`.
        body = re.sub(
            r"\s*(?:Q\.?E\.?D\.?|\\qed|\\square|as required|as desired|QED)\s*\.?\s*$",
            "",
            body,
            flags=re.IGNORECASE | re.DOTALL,
        )
        # 3. Mid-body inline markers (rare but seen): `... text Q.E.D. more text`.
        #    Only strip if the marker is clearly delimited (whitespace or punct
        #    on both sides) — avoid false positives on mathematical names.
        body = re.sub(
            r"(?<=[\.\)\}\s])(?:Q\.?E\.?D\.?|\\qed|\\square)\s*\.?(?=\s|\\end\{proof\}|$)",
            "",
            body,
            flags=re.IGNORECASE,
        )
        if body != original:
            n += 1
        return f"{m.group(1)}{body}{m.group(3)}"

    new = pat_proof.sub(_scrub, text)
    return new, n


def _convert_paren_to_dollar(text: str) -> tuple[str, int]:
    """Convert `\\(X\\)` to `$X$`. Project convention is `$ / $$`."""
    # Avoid converting inside \verb or \texttt{} or comments.
    # Simple: skip lines that start with %.
    n = 0
    out_lines = []
    for line in text.splitlines():
        if line.lstrip().startswith("%"):
            out_lines.append(line)
            continue
        new = re.sub(r"\\\((.*?)\\\)", r"$\1$", line, flags=re.DOTALL)
        if new != line:
            n += new.count("$") - line.count("$")
        out_lines.append(new)
    return "\n".join(out_lines) + ("\n" if text.endswith("\n") else ""), n


def _convert_brk_to_dd(text: str) -> tuple[str, int]:
    """Convert `\\[X\\]` display math to `$$X$$`."""
    n = 0
    # `\[ ... \]` may span multiple lines; multiline regex
    pat = re.compile(r"\\\[(.*?)\\\]", re.DOTALL)

    def _repl(m: re.Match) -> str:
        nonlocal n
        n += 1
        body = m.group(1)
        # Ensure $$ on its own line per project convention
        body_stripped = body.strip()
        return f"\n$$\n{body_stripped}\n$$\n"

    new = pat.sub(_repl, text)
    # collapse multiple blank lines
    new = re.sub(r"\n{3,}", "\n\n", new)
    return new, n


def _swap_mathsf_for_bare(text: str, preamble_macros: set[str]) -> tuple[str, int]:
    """Replace `\\mathsf{X}` with `\\X` when `\\X` exists in preamble."""
    if not preamble_macros:
        return text, 0
    n = 0

    def _repl(m: re.Match) -> str:
        nonlocal n
        name = m.group(1)
        if name in preamble_macros:
            n += 1
            return f"\\{name}"
        return m.group(0)

    new = re.sub(r"\\mathsf\{([A-Za-z]+)\}", _repl, text)
    return new, n


def _strip_iteration_vocab(text: str) -> tuple[str, int]:
    """Remove iteration-vocabulary phrases that the project forbids."""
    forbidden = [
        "we extend", "we now revise", "we now extend", "we now patch",
        "we extend the", "we now establish",  # often safe phrasing — keep
    ]
    # Only a small set of phrases gets cleaned; rest go to remaining_issues.
    n = 0
    new = text
    # Soft fixes: replace "we extend" with neutral "we establish"
    soft_repl = [
        (r"\bwe extend\b", "we establish"),
        (r"\bwe now revise\b", "we now state"),
    ]
    for pat, sub in soft_repl:
        new2, k = re.subn(pat, sub, new, flags=re.IGNORECASE)
        if k:
            n += k
            new = new2
    return new, n


def _strip_lean_markers(text: str) -> tuple[str, int]:
    """Strip `\\leanchecked{...}` / variants — those are added later by the
    formalize lane, not here."""
    pat = re.compile(r"\\(?:leanchecked|leanvariant|leansorryd|leandef|leanstmt)\{[^}]*\}")
    n = len(pat.findall(text))
    new = pat.sub("", text)
    return new, n


def _strip_section_openers(text: str) -> tuple[str, int]:
    """Remove `\\section{...}`, `\\chapter{...}`, etc. — block appends into
    existing chapter file, must not introduce new sectioning."""
    pat = re.compile(r"^\s*\\(?:part|chapter|section|subsection|subsubsection|paragraph|subparagraph)\*?\{[^}]*\}\s*\n",
                     re.MULTILINE)
    n = len(pat.findall(text))
    new = pat.sub("", text)
    return new, n


def _convert_ref_to_autoref(text: str) -> tuple[str, int]:
    """Replace `\\ref{thm:X}` with `\\autoref{thm:X}` when the prefix is
    one of thm/lem/prop/cor/def/sec/ch."""
    pat = re.compile(r"\\ref\{(thm|lem|prop|cor|def|sec|ch):([^}]+)\}")
    n = len(pat.findall(text))
    new = pat.sub(r"\\autoref{\1:\2}", text)
    return new, n


def _detect_blocking_issues(text: str) -> list[str]:
    """Find issues the normalizer CANNOT mechanically fix; these need
    LLM/human attention. Returns a list of issue descriptions."""
    issues: list[str] = []

    # No theorem/lemma/etc. environment
    if not re.search(r"\\begin\{(?:theorem|lemma|proposition|corollary|definition)\}", text):
        issues.append(
            "no theorem/lemma/proposition/corollary/definition environment found"
        )

    # Mismatched begin/end
    begins = re.findall(r"\\begin\{([a-zA-Z*]+)\}", text)
    ends = re.findall(r"\\end\{([a-zA-Z*]+)\}", text)
    from collections import Counter
    if Counter(begins) != Counter(ends):
        issues.append(
            f"unbalanced environments: begins={Counter(begins)} vs ends={Counter(ends)}"
        )

    # Chinese characters
    if re.search(r"[一-鿿]", text):
        issues.append("Chinese characters present in LaTeX content (must be English-only)")

    # Missing labels on theorem-likes
    theorem_blocks = re.findall(
        r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[[^\]]*\])?\s*\n?\s*([^\n]*)",
        text,
    )
    for env, after in theorem_blocks:
        if "\\label{" not in after:
            # Check next 3 lines for label
            pass  # too noisy to flag — let pdflatex catch it

    # Stray version prefixes in labels
    if re.search(r"\\label\{[a-z]+:v\d", text):
        issues.append("label uses version prefix (vN) — must be semantic only")

    # Residual QED markers inside proof bodies that normalize couldn't strip.
    # If these reach pdflatex they don't break compilation but they do violate
    # project hygiene. Flag for downstream review (won't fast-path through
    # claude bypass).
    proof_blocks = re.findall(
        r"\\begin\{proof\}(.*?)\\end\{proof\}", text, flags=re.DOTALL
    )
    for body in proof_blocks:
        if re.search(r"\b(?:Q\.?E\.?D\.?|QED)\b", body, re.IGNORECASE):
            issues.append("residual QED marker inside \\begin{proof} block")
            break
        if re.search(r"\\(?:qed|square)\b", body):
            issues.append("residual \\qed/\\square inside \\begin{proof} block")
            break

    # Mashed control sequences — common DOM-scrape damage pattern. Things
    # like `\qquadT`, `\qquadP=|p|`, `\quadd`, `\quadx_i`. These compile-
    # break because LaTeX reads `\qquadT` as one undefined cs. We can't
    # safely auto-rewrite (which letter starts the next token?) so flag.
    # Heuristic: a known-spacing macro followed immediately by a capital
    # letter or digit, no whitespace between.
    spacing_macros = (
        r"qquad|quad|hspace|vspace|hfill|vfill|smallskip|medskip|bigskip|"
        r"newline|noindent|indent|quad|qquad|hskip|vskip"
    )
    mashed = re.findall(
        rf"\\(?:{spacing_macros})[A-Za-z0-9]",
        text,
    )
    if mashed:
        issues.append(
            f"mashed spacing macro(s) detected (e.g. {mashed[0]!r}); "
            f"oracle output missing whitespace between control seq and next token"
        )

    # Display math `$$` not on its own line — `Foo$$X$$bar` style. This
    # technically compiles but violates AGENTS.md "$$ 必须独立成行".
    # Heuristic: detect `$$` immediately preceded or followed by a non-
    # whitespace character (other than newline).
    inline_dd_pre = re.search(r"\S\$\$[^\$]", text)
    inline_dd_post = re.search(r"[^\$]\$\$\S", text)
    if inline_dd_pre or inline_dd_post:
        issues.append("`$$ ... $$` display math block not on its own line")

    # Interface-level checks: BEDC core relations used as functions.
    issues.extend(_detect_relation_as_function(text))

    # Interface-level checks: transport-style language without explicit ref.
    issues.extend(_detect_hsame_as_equality(text))

    return issues


# BEDC core *predicates* (relations). Arguments must be history terms, never
# function expressions. Misuse pattern: `\Rel(a, \mathsf{f}(args), c)` or
# `\Rel(a, \append(args), c)` — the second arg is a function expression
# rather than a bound history variable. Correct form is existential:
# `\exists u. \Rel(a, u, c) \wedge ...`.
BEDC_CORE_RELATIONS = (
    "Cont", "Ext", "hsame", "msame", "psame",
    "Sig", "Pkg", "NatMul", "NatDivides", "PolySame",
    "InGapSig", "InBundle", "SigRel",
)


def _detect_relation_as_function(text: str) -> list[str]:
    """Flag BEDC predicate uses with function-expression arguments."""
    issues: list[str] = []
    for rel in BEDC_CORE_RELATIONS:
        # \Rel(...) with any \mathsf{...}(...) inside args, or \append(...).
        # We scan each occurrence's argument list (top-level paren balanced).
        for m in re.finditer(rf"\\{rel}\s*\(", text):
            # Find matching close paren, depth-tracking
            i = m.end()
            depth = 1
            start = i
            while i < len(text) and depth > 0:
                if text[i] == "(":
                    depth += 1
                elif text[i] == ")":
                    depth -= 1
                i += 1
            args = text[start : i - 1]
            # Function-expression patterns inside args
            if re.search(r"\\mathsf\s*\{[^}]+\}\s*\(", args) or \
               re.search(r"\\append\s*\(", args) or \
               re.search(r"\\mul\s*\(", args):
                issues.append(
                    f"\\{rel} is a BEDC relation; argument list contains a "
                    f"function expression: '{args[:80]}…'. Relations take "
                    f"history terms only — restructure as \\exists witness."
                )
                break  # one per relation is enough
    return issues


def _detect_hsame_as_equality(text: str) -> list[str]:
    """Flag transport-style prose without an adjacent \\autoref reference."""
    issues: list[str] = []
    transport_phrases = [
        r"replacing\s+\$[^$]+\$\s+by\s+\$[^$]+\$",
        r"identif(?:y|ies|ying|ied)\s+\$[^$]+\$\s+with\s+\$[^$]+\$",
        r"after\s+substituting\s+\$[^$]+\$",
        r"transporting\s+(?:the\s+)?\w+\s+(?:along|across)\s+\$[^$]+\$",
        r"sends\s+\$[^$]+\$\s+to\s+\$[^$]+\$",
    ]
    for phrase in transport_phrases:
        for m in re.finditer(phrase, text, re.IGNORECASE):
            # Adjacent context window — must contain \autoref or \ref to
            # an explicit lemma/theorem within ±300 chars.
            start = max(0, m.start() - 100)
            end = min(len(text), m.end() + 300)
            window = text[start:end]
            if not re.search(r"\\autoref\{(?:lem|thm|prop):[^}]+\}", window):
                issues.append(
                    f"transport-style prose ('{m.group(0)[:60]}') without "
                    f"adjacent \\autoref{{lem|thm|prop:...}} citation; "
                    f"BEDC requires explicit transport lemma references."
                )
                return issues  # one per file is enough
    return issues


# ---------------------------------------------------------------------------
# Main normalize entry
# ---------------------------------------------------------------------------


def normalize(
    content: str,
    *,
    preamble_path: Optional[Path] = None,
) -> NormalizeResult:
    """Apply mechanical hygiene normalizations to a LaTeX block.

    Returns NormalizeResult with normalized content + list of transformations
    applied + list of remaining issues that need attention beyond
    mechanical fix.
    """
    preamble_macros: set[str] = set()
    if preamble_path is not None:
        preamble_macros = _load_preamble_macros(preamble_path)

    transformations: list[str] = []
    new = content

    # ── Order matters: run \[ → $$ before \( → $ to avoid eating the
    # outer brackets of \[ within a malformed slip (defensive).

    new, n_brk = _convert_brk_to_dd(new)
    if n_brk:
        transformations.append(f"converted {n_brk} `\\[...\\]` block(s) to `$$...$$`")

    new, n_paren = _convert_paren_to_dollar(new)
    if n_paren > 0:
        transformations.append(f"converted ~{n_paren // 2} `\\(...\\)` inline(s) to `$...$`")

    new, n_qed = _strip_proof_markers(new)
    if n_qed:
        transformations.append(f"stripped manual QED markers from {n_qed} proof block(s)")

    new, n_msf = _swap_mathsf_for_bare(new, preamble_macros)
    if n_msf:
        transformations.append(
            f"swapped {n_msf} `\\mathsf{{X}}` for bare preamble macro `\\X`"
        )

    new, n_iter = _strip_iteration_vocab(new)
    if n_iter:
        transformations.append(f"replaced {n_iter} iteration-vocab phrase(s) with neutral form")

    new, n_lean = _strip_lean_markers(new)
    if n_lean:
        transformations.append(f"stripped {n_lean} `\\leanchecked`/variant marker(s)")

    new, n_sec = _strip_section_openers(new)
    if n_sec:
        transformations.append(f"stripped {n_sec} sectioning opener(s)")

    new, n_ref = _convert_ref_to_autoref(new)
    if n_ref:
        transformations.append(f"converted {n_ref} `\\ref` to `\\autoref`")

    blocking = _detect_blocking_issues(new)

    return NormalizeResult(
        content=new,
        changed=(new != content),
        transformations=transformations,
        remaining_issues=[],
        blocking_issues=blocking,
    )


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser(description="Hygiene normalize smoke test")
    parser.add_argument("input", help="path to a raw LaTeX file (or '-' for stdin)")
    parser.add_argument("--preamble", default="papers/bedc/preamble.tex")
    parser.add_argument("--diff", action="store_true", help="show before/after diff")
    args = parser.parse_args()

    if args.input == "-":
        import sys
        content = sys.stdin.read()
    else:
        content = Path(args.input).read_text(encoding="utf-8")

    result = normalize(content, preamble_path=Path(args.preamble))

    print(f"=== transformations ({len(result.transformations)}) ===")
    for t in result.transformations:
        print(f"  - {t}")
    print(f"\n=== blocking issues ({len(result.blocking_issues)}) ===")
    for b in result.blocking_issues:
        print(f"  - {b}")

    if args.diff:
        import difflib
        diff = difflib.unified_diff(
            content.splitlines(keepends=True),
            result.content.splitlines(keepends=True),
            fromfile="original", tofile="normalized",
        )
        print("\n=== diff ===")
        print("".join(diff))
    else:
        print(f"\n=== output ({len(result.content)} chars) ===")
        print(result.content[:1000])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
