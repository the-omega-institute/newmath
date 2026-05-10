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

### B-596 - Holomorphic strict iterated chain length cancellation determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Holomorphic strict iterated chain length cancellation determinacy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If two strict iterated complex-differentiability chains from a unary seed agree on selected endpoint $h$, then their iteration-index histories are $\hsame$-equal under the displayed unary classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/holomorphic/predicate_and_iterations.tex`

Rationale:
Determinism / no-confusion result on the IteratedStrictCplxDiff inductive — exactly the kind of structural target B writes (compare B-507 halting-meta-loop, B-452 ODE concatenation endpoint determinacy). The 12 surrounding theorems on this inductive include concatenation, transport, prefix readback, endpoint-not-empty, but no length cancellation, leaving a clear no-confusion gap. Lands in predicate_and_iterations.tex (277 lines, room) and proof skeleton parallels endpoint-hsame-absurd plus prefix readback. Not a parameter echo: it is the missing length-determinacy companion, not a re-statement of a source equivalence.

---
