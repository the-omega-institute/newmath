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


### B-603 - Ideal sum is monotone in inclusion preorder

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ideal sum is monotone in inclusion preorder |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For ideals I, I', J, J' of a RingUp R, if I \preceq_R I' and J \preceq_R J' (def:ideal-inclusion-predicate:94), then (I+_R J) \preceq_R (I'+_R J') as carried predicates, with each sum-membership witness routed through the two given inclusion implications and the same additive-decomposition row.

Local inputs:
- `papers/bedc/parts/concrete_instances/ideal/02_lattice_sum_surface.tex`

Rationale:
The ideal-inclusion preorder is defined at def:ideal-inclusion-predicate:94 and used in thm:ideal-sum-least-upper-bound:158 and thm:ideal-intersection-greatest-lower-bound:272, but no theorem records that the sum constructor is monotone in this order. Without monotonicity, the sum is exhibited only as a particular LUB rather than as a functorial join in the ideal lattice, and downstream consumers cannot transport sum memberships across refinements of the input ideals. Single-implication concrete claim (not biconditional, not transport-only). Distinct from B-601 (commutativity), thm:ideal-sum-closure (closure under ring rows), and thm:ideal-sum-least-upper-bound (which just exposes K as one upper bound, not its monotonicity). Proof is direct: unpack a sum witness for (I+J)(z), apply the two inclusions, repack. Non-trivial because both inclusion-witness composition and additive-decomposition repacking must agree.

---


### B-604 - ConvexSet pointwise intersection is commutative as a carrier predicate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ConvexSet pointwise intersection is commutative as a carrier predicate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
For ConvexSetUp certificates with convex carriers C, D over the same scalar FieldUp and vector VecSpaceUp data, the predicates C\cap_{ConvexSetUp}D and D\cap_{ConvexSetUp}C agree at every endpoint z:V; the witness pair (C(z), D(z)) and (D(z), C(z)) are interchanged with no change to the displayed scalar, addition, or affine-combination rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`

Rationale:
186_convexset_namecert_construction.tex (432 lines, room available, not yet split) defines pointwise intersection at def:convexset-pointwise-intersection-carrier:197 and proves intersection closure at thm:convexset-pointwise-intersection-affine-combination-closure:206, but no theorem states commutativity of the binary intersection constructor. This is the same shape of sister gap that motivated B-601 ideal sum commutativity: the closure theorem treats the two input carriers asymmetrically, and a symmetric-swap row is needed before any later finite-intersection or arbitrary-intersection generalization can cite a commutative monoid structure. Single-implication biconditional. Non-trivial enough to be a distinct theorem (proof has to repackage the conjunction of two ConvexSet carrier-supports through the shared FieldUp / VecSpaceUp data named in the definition, not just bare \land-commutativity). Grep on `intersection.*commut|commut.*intersection|swap.*intersect` in this file returns nothing.

---

