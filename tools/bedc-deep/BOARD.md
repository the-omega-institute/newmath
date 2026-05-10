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

### B-602 - Ideal sum associativity (I+J)+K coincides with I+(J+K) as carrier predicates

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ideal sum associativity (I+J)+K coincides with I+(J+K) as carrier predicates |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For ideals I, J, K of a RingUp R, the iterated ideal sums (I+_R J)+_R K and I+_R (J+_R K) coincide as carrier predicates on BHist, with matching ambient ring carrier rows, regrouped additive-decomposition witnesses obtained from RingUp additive associativity, and identical Pkg provenance.

Local inputs:
- `papers/bedc/parts/concrete_instances/ideal/02_lattice_sum_surface.tex`

Rationale:
ideal/02_lattice_sum_surface.tex (336 lines, well below cap) just gained ideal sum commutativity as B-601 (lines 295–335) but the symmetric sister law — associativity — is missing. The file already builds the lattice picture (intersection closure thm:ideal-intersection-closure:48; sum closure thm:ideal-sum-closure:103; sum LUB thm:ideal-sum-least-upper-bound:158; intersection GLB thm:ideal-intersection-greatest-lower-bound:272) so an associativity row is the natural completion of the ideal lattice axioms before any further ideal-product or ideal-quotient algebra is opened. Proof is non-trivial: pulls additive associativity from RingUp's stability certificate, threads classifier transitivity through nested existential decomposition witnesses (def:ideal-sum-predicate:84), and is concrete (not abstract carrier transport). No existing label or Lean target collides (grep on `ideal-sum-associativ` and `IdealSum.*Assoc` returns nothing in papers/bedc/ or lean4/BEDC/Derived/IdealUp/).

---
