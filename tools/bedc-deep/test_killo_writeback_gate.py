#!/usr/bin/env python3
"""Focused checks for Stage 2 killo-golden gate routing."""

import importlib.util
import sys
import tempfile
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("killo_golden_writeback.py")
spec = importlib.util.spec_from_file_location("killo_golden_writeback", MODULE_PATH)
assert spec is not None and spec.loader is not None
killo_golden_writeback = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = killo_golden_writeback
spec.loader.exec_module(killo_golden_writeback)

HYGIENE_PATH = Path(__file__).with_name("hygiene_normalize.py")
hygiene_spec = importlib.util.spec_from_file_location("hygiene_normalize", HYGIENE_PATH)
assert hygiene_spec is not None and hygiene_spec.loader is not None
hygiene_normalize = importlib.util.module_from_spec(hygiene_spec)
sys.modules[hygiene_spec.name] = hygiene_normalize
hygiene_spec.loader.exec_module(hygiene_normalize)


def test_multiple_body_envs_rejected_as_not_minimal() -> None:
    content = r"""
\begin{lemma}
\label{lem:alpha}
Alpha holds.
\end{lemma}

\begin{proposition}
\label{prop:beta}
Beta holds.
\end{proposition}
"""
    reasons, codes = killo_golden_writeback._deterministic_theory_rejections(
        content,
        target_title="Alpha beta packet",
        target_tex_file="papers/bedc/parts/concrete_instances/example.tex",
    )
    assert "not_minimal_multiple_surfaces" in codes
    assert any("one minimal" in reason for reason in reasons)


def test_append_after_closurestatus_rejected_for_theorem_like_content() -> None:
    target = killo_golden_writeback.REPO_ROOT / "papers" / "bedc" / "parts" / "_tmp_stage2_gate_closure.tex"
    target.write_text(
        "\\begin{closurestatus}{\\TmpUp}\n\\end{closurestatus}\n",
        encoding="utf-8",
    )
    original_resolve = killo_golden_writeback._resolve_target_tex
    killo_golden_writeback._resolve_target_tex = lambda _path: target
    try:
        reasons, codes = killo_golden_writeback._deterministic_theory_rejections(
            "\\begin{lemma}\n\\label{lem:tmp}\nTmp.\n\\end{lemma}\n",
            target_title="Tmp",
            target_tex_file=str(target.relative_to(killo_golden_writeback.REPO_ROOT)),
        )
    finally:
        killo_golden_writeback._resolve_target_tex = original_resolve
        target.unlink(missing_ok=True)
    assert "append_after_closurestatus" in codes
    assert any("closurestatus" in reason for reason in reasons)


def test_verification_axis_surface_rejected_before_codex_gate() -> None:
    content = (
        "\\begin{theorem}[Closed-term substitution boundary downstream Lean-target coverage]\n"
        "\\label{thm:closed-term-substitution-boundary-downstream-lean-target-coverage}\n"
        "For the Lean target $\\mathsf{BEDC.Derived.X.single\\_carrier\\_alignment}$, every consumer is local.\n"
        "\\end{theorem}\n"
    )
    reasons, codes = killo_golden_writeback._deterministic_theory_rejections(
        content,
        target_title="Closed term substitution boundary Lean target downstream coverage lemma",
        target_tex_file="papers/bedc/parts/concrete_instances/example.tex",
    )
    assert "verification_axis_surface" in codes
    assert any("verification-axis" in reason for reason in reasons)


def test_normalizer_discovers_preamble_input_macros() -> None:
    result = hygiene_normalize.normalize(
        "The witness is $\\mathsf{UnaryHistory}$ and $\\mathsf{BHist}$.\n",
        preamble_path=killo_golden_writeback.REPO_ROOT / "papers" / "bedc" / "preamble.tex",
    )
    assert "$\\UnaryHistory$" in result.content
    assert "$\\BHist$" in result.content
    assert result.transformations


def test_writeback_uses_codex_gate_directly() -> None:
    target = killo_golden_writeback.REPO_ROOT / "papers" / "bedc" / "parts" / "_tmp_stage2_gate_fallback.tex"
    target.write_text("% temporary test target\n", encoding="utf-8")
    raw = Path(tempfile.gettempdir()) / "stage2_gate_fallback_raw.tex"
    content = "\\begin{lemma}\n\\label{lem:stage2-gate-fallback}\nFallback holds.\n\\end{lemma}\n"
    raw.write_text(content, encoding="utf-8")

    calls = {"codex": 0, "make": 0}
    original_codex = killo_golden_writeback.codex_json_fallback
    original_make = killo_golden_writeback._make_paper
    try:
        def fake_codex(_prompt: str, **_kwargs):
            calls["codex"] += 1
            return (
                True,
                {
                    "verdict": "accept",
                    "tex_file": str(target.relative_to(killo_golden_writeback.REPO_ROOT)),
                    "content": content,
                    "rejection_reasons": [],
                },
                '{"verdict":"accept"}',
                "",
            )

        def fake_make():
            calls["make"] += 1
            return (True, "ok")

        killo_golden_writeback.codex_json_fallback = fake_codex
        killo_golden_writeback._make_paper = fake_make

        result = killo_golden_writeback.writeback(
            target_id="B-test",
            target_title="Fallback gate",
            transcript_dir=Path(tempfile.gettempdir()),
            raw_latex_path=raw,
            suggested_target_tex=str(target.relative_to(killo_golden_writeback.REPO_ROOT)),
        )
    finally:
        killo_golden_writeback.codex_json_fallback = original_codex
        killo_golden_writeback._make_paper = original_make
        target.unlink(missing_ok=True)
        raw.unlink(missing_ok=True)

    assert result.ok
    assert result.verdict == "accept"
    assert calls == {"codex": 1, "make": 1}


if __name__ == "__main__":
    test_multiple_body_envs_rejected_as_not_minimal()
    test_append_after_closurestatus_rejected_for_theorem_like_content()
    test_verification_axis_surface_rejected_before_codex_gate()
    test_normalizer_discovers_preamble_input_macros()
    test_writeback_uses_codex_gate_directly()
    print("test_killo_writeback_gate: ok")
