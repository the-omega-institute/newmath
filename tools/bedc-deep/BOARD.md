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

### B-600 - SpinGroup conjugation action is multiplicative under the spin group product

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | SpinGroup conjugation action is multiplicative under the spin group product |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If s, t are accepted SpinGroupUp packets and v is a Clifford-vector row, then the conjugation action of s*t on v classifies (under hsame on Clifford rows) to the composite of conjugation by s applied to conjugation by t on v, with the same orthogonal-action endpoint and Pkg provenance.

Local inputs:
- `papers/bedc/parts/concrete_instances/spingroup/boundary_consumer_exactness.tex`
- `papers/bedc/parts/concrete_instances/spingroup/ledger_exclusion_surface.tex`

Rationale:
Frontier concrete object. SpinGroupUp exposes a conjugation action (thm:spingroup-conjugation-action-readback at boundary_consumer_exactness.tex:27) but no homomorphism law for the action under the spin product. The shape mirrors BOARD B-581 (AdjointRepUp Ad(gh) ~ Ad(g) o Ad(h)) but on a distinct carrier (SpinGroup/Clifford rather than adjoint rep on Lie algebra), so it is not a duplicate or paraphrase. Construction unfolds the conjugation readback for s*t into a Clifford product-inverse-product spine on s,t,v,t-inverse,s-inverse, then applies Clifford associativity and inverse-product readback. Lands in boundary_consumer_exactness.tex (76 lines). Oracle_likely route: Clifford-side associativity and inverse-product alignment require careful spine bookkeeping.

---

### B-601 - Ideal sum is commutative as a sub-ideal predicate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Ideal sum is commutative as a sub-ideal predicate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
For ideals I, J of an ambient RingUp R, the ideal sum I + J coincides with J + I as carrier predicates, with matching ambient ring carrier rows, swapped additive-decomposition witnesses, and identical Pkg provenance.

Local inputs:
- `papers/bedc/parts/concrete_instances/ideal/02_lattice_sum_surface.tex`

Rationale:
Missing companion in the ideal lattice surface. ideal/02_lattice_sum_surface.tex declares thm:ideal-sum-closure (line 103) and thm:ideal-sum-least-upper-bound (line 158); the meet side has thm:ideal-intersection-greatest-lower-bound (BOARD B-555). Commutativity of the join is fundamental and used implicitly whenever sums are written, yet no thm:ideal-sum-commutativity / thm:ideal-sum-symmetric label exists under papers/bedc/parts/. Not a transport echo: it is a genuine concrete closure of the ideal-sum predicate using the ambient ring's additive commutativity row. Codex_close in 1-3 rounds; lands in lattice_sum_surface.tex which is well under the 800-line cap.

---
