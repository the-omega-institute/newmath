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

### B-643 - Modular-form empty-coefficient q-expansion carrier classifies under shared source rows

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Modular-form empty-coefficient q-expansion carrier classifies under shared source rows |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
Two ModularFormUp q-expansion carrier rows whose q-expansion coefficient observation rows are both the empty BHist row and that share the same HolomorphicUp source row and AutomorphicUp source row over the same weight and congruence-subgroup context are classified by the modular-form congruence classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/230_modularform_namecert_construction.tex`

Rationale:
230_modularform_namecert_construction.tex (74 lines, 3 theorems: holomorphic source scope, automorphic transport stability, namecert obligation surface) defines def:modularform-bhist-qexpansion-carrier with a 'finite q-expansion coefficient observation row' but never writes the empty-coefficient base case despite it being the natural inhabitation witness. ModularForm has zero BOARD targets. This is the same shape as B-538 (Quadrature empty-node sum is zero) and B-527 (Independence empty index family) — exposed empty-case classifier inhabitation in an obligation-only chapter.

---

