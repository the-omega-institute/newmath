# BEDC Deep Reasoning Board

Purpose: drive a self-iterating BEDC paper-extension loop. Each entry below is
a target the oracle deep-reasoning loop runs to a complete result, then
appends as canonical current-state LaTeX into `papers/bedc/parts/`. The
downstream `lean4/scripts/codex_formalize.py` lane (on dev) picks up new
theorem sites by scanning the paper.

Lane edge:
- This lane never edits `lean4/`. The handshake to formalization is the
  appended LaTeX in `papers/bedc/parts/<theme>/<concept>.tex` (no marker
  macros — those are added by `codex_formalize.py` after the Lean target lands).
- New targets are auto-spawned by Stage 1.5 topic discovery and appended to
  this board with `Status: Candidate (auto-spawned)`.

Each target card carries enough context (Object, Local inputs) for the loop
to build its initial prompt without external lookups.

---

### B-645 - Closure-reflection obstruction completeness (converse to Theorem 3.10)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Closure-reflection obstruction completeness (converse to Theorem 3.10) |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 9/10 |

Problem:
If ¬ClosureReflect(Π) for a generated probe bundle Π, then there exist signatures a, b, c, d and tokens p, q, r witnessing the four-edge TokIntro/hsame configuration of thm:equivalence-closure-reflection-obstruction, so that obstruction characterises every closure-reflection failure.

Local inputs:
- `papers/bedc/parts/proof_obligations/psame_design.tex`

Rationale:
Theorem 3.10 in psame_design.tex supplies only the sufficient direction (the four-edge configuration forces ¬ClosureReflect ∧ ¬TokUnique). The converse — that every closure-reflection failure factors through such a finite four-edge witness — is a genuine completeness statement and closes the boundary against the positive Conditional Schema (Proposition 3.6). It is a true obstruction-characterisation theorem (Category 3 in BOARD vocabulary), not a notation variant of any existing entry, and lands in proof_obligations where psame_design.tex (374 lines) has child-file room. Worth a target slot because pairing the necessity-from-sufficiency closes a load-bearing gap in the equivalence-closure obstruction theory rather than echoing an existing classifier transport.

---
