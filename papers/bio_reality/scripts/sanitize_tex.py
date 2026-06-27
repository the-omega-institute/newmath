#!/usr/bin/env python3
"""Build-time sanitizer for codex-emitted invalid LaTeX in bio_reality namecerts.

The codex-driven namecert writer intermittently emits constructs that make
pdflatex fail and chronically gate bio-K:
  - bare ``^\\*`` (superscript of the discretionary-times macro) -> ``^{*}``
  - literal Unicode math/Greek characters (Δ, ρ, ², ≈, →, …) that pdflatex,
    without unicode setup, rejects with "Unicode character ... not set up".

Rewrite both to well-formed LaTeX. ``\\ensuremath{...}`` is safe in either text
or math mode, so wrapping a literal symbol works wherever codex placed it.
Idempotent (after a pass there are no literals left to match), runs before
every build, and survives the per-cycle regeneration of the .tex files.

Pure stdlib. Walks parts/**/*.tex relative to the paper dir (this file's
grandparent).
"""
from __future__ import annotations
import pathlib
import re

# Unicode codepoint -> LaTeX body (wrapped in \ensuremath at substitution time).
_MAP = {
    # Greek lower
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta",
    "ε": r"\epsilon", "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta",
    "ι": r"\iota", "κ": r"\kappa", "λ": r"\lambda", "μ": r"\mu",
    "ν": r"\nu", "ξ": r"\xi", "π": r"\pi", "ρ": r"\rho",
    "ς": r"\varsigma", "σ": r"\sigma", "τ": r"\tau", "υ": r"\upsilon",
    "φ": r"\phi", "χ": r"\chi", "ψ": r"\psi", "ω": r"\omega",
    # Greek upper
    "Γ": r"\Gamma", "Δ": r"\Delta", "Θ": r"\Theta", "Λ": r"\Lambda",
    "Ξ": r"\Xi", "Π": r"\Pi", "Σ": r"\Sigma", "Υ": r"\Upsilon",
    "Φ": r"\Phi", "Ψ": r"\Psi", "Ω": r"\Omega",
    # superscript digits
    "⁰": r"^{0}", "¹": r"^{1}", "²": r"^{2}", "³": r"^{3}", "⁴": r"^{4}",
    "⁵": r"^{5}", "⁶": r"^{6}", "⁷": r"^{7}", "⁸": r"^{8}", "⁹": r"^{9}",
    # subscript digits
    "₀": r"_{0}", "₁": r"_{1}", "₂": r"_{2}", "₃": r"_{3}", "₄": r"_{4}",
    "₅": r"_{5}", "₆": r"_{6}", "₇": r"_{7}", "₈": r"_{8}", "₉": r"_{9}",
    # relations / operators / arrows codex uses in stats prose
    "×": r"\times", "÷": r"\div", "±": r"\pm", "∓": r"\mp",
    "≈": r"\approx", "≤": r"\leq", "≥": r"\geq", "≠": r"\neq",
    "≡": r"\equiv", "∼": r"\sim", "∝": r"\propto",
    "→": r"\to", "←": r"\leftarrow", "↔": r"\leftrightarrow",
    "⇒": r"\Rightarrow", "⇐": r"\Leftarrow", "⇔": r"\Leftrightarrow",
    "∞": r"\infty", "∑": r"\sum", "∏": r"\prod", "√": r"\surd",
    "∈": r"\in", "∉": r"\notin", "∩": r"\cap", "∪": r"\cup",
    "⊂": r"\subset", "⊆": r"\subseteq", "⊃": r"\supset",
    "∂": r"\partial", "∇": r"\nabla", "∀": r"\forall", "∃": r"\exists",
    "·": r"\cdot", "•": r"\bullet", "°": r"^{\circ}",
}
# characters that should become plain ASCII rather than math
_ASCII = {
    "−": "-",   # U+2212 minus sign -> hyphen
    "–": "--",  # en dash
    "—": "---", # em dash
    "’": "'", "‘": "'", "“": "``", "”": "''",
    "…": r"\ldots ",
    " ": " ",  # non-breaking space
}

_SYM_RE = re.compile("|".join(re.escape(k) for k in _MAP))
_ASCII_RE = re.compile("|".join(re.escape(k) for k in _ASCII))
_CARET_STAR_RE = re.compile(r"\^\\\*")


def sanitize_text(s: str) -> str:
    s = _CARET_STAR_RE.sub("^{*}", s)
    s = _ASCII_RE.sub(lambda m: _ASCII[m.group(0)], s)
    s = _SYM_RE.sub(lambda m: r"\ensuremath{" + _MAP[m.group(0)] + "}", s)
    return s


def main() -> None:
    paper_dir = pathlib.Path(__file__).resolve().parent.parent
    parts = paper_dir / "parts"
    changed = 0
    for p in parts.rglob("*.tex"):
        try:
            orig = p.read_text(encoding="utf-8")
        except Exception:
            continue
        fixed = sanitize_text(orig)
        if fixed != orig:
            p.write_text(fixed, encoding="utf-8")
            changed += 1
    print(f"sanitize_tex: {changed} file(s) rewritten")


if __name__ == "__main__":
    main()
