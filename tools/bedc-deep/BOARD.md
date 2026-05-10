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

### B-598 - Measure finite-union associativity over three pairwise-disjoint events

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Measure finite-union associativity over three pairwise-disjoint events |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
For pairwise-disjoint measurable events A,B,C in the same fiber, the binary unions (A union B) union C and A union (B union C) are classifier-equal as measurable events with equal real-valued measure.

Local inputs:
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`
- `papers/bedc/parts/concrete_instances/measure/finite_additivity_readback.tex`

Rationale:
Existing theorems include thm:measure-finite-disjoint-union-additivity and BOARD B-530 'MeasureUp triple-union subadditivity'. Subadditivity is INEQUALITY; associativity is EQUALITY of the bracketed unions and is not the same theorem. grep -nE 'measure.*assoc|union.*assoc' under measure/ returns only one informal reference (root_finite_disjoint_event_envelope.tex:113). This is a clean closure law on the binary-union row of def:measure-sigma-algebra-carrier-surface (carrier_surface_rows.tex L1-32).

---

