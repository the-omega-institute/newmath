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

### B-605 - Ideal sum is the least upper bound under inclusion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Ideal sum is the least upper bound under inclusion |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
In IdealUp with inclusion preorder, if I≤K and J≤K then I+J≤K, and I≤I+J, J≤I+J, so I+J is the least upper bound of I,J.

Local inputs:
- `papers/bedc/parts/concrete_instances/ideal/02_lattice_sum_surface.tex`

Rationale:
Natural structural lift of the recently-closed B-601/B-602/B-603 cluster (commutativity, associativity, monotonicity of ideal sum). The LUB / lattice-join formulation has not landed yet, and B-555 only gives the dual intersection-as-GLB. Proof reuses the existing sum-membership predicate plus the inclusion preorder, no external structure.

---


### B-606 - ConvexSet intersection is the inclusion meet

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | ConvexSet intersection is the inclusion meet |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
In ConvexSetUp with pointwise intersection carrier, if E⊆C and E⊆D then E⊆C∩D, plus C∩D⊆C and C∩D⊆D, so C∩D is the greatest lower bound of C,D in the inclusion preorder.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`

Rationale:
Direct order-theoretic extension of B-604 (intersection commutativity). Distinct from B-555 (ideal-side GLB) since the carrier and convex-combination obligations differ. Universal-property phrasing requires both projection bounds plus universality, so it is more than a paraphrase. Lands in a non-cap file.

---


### B-607 - Polynomial raw multiplication associativity up to trim

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Polynomial raw multiplication associativity up to trim |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
In PolynomialUp with literal raw multiplication and add-trim classifier, for any carried representatives p,q,r the canonical add-trim of rawMul(rawMul(p,q),r) classifies with rawMul(p,rawMul(q,r)).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_multiplication.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex`

Rationale:
Major structural gap: existing BOARD has identities (B-592/B-593), zero absorption (B-570), and distributivity (B-579/B-587) but no associativity for rawMul. Closing this is the main missing pillar between an operation package and a true semiring-like structure on PolynomialUp. Concrete inductive proof on literal recursion and add-trim algebra, no abstract carrier transport.

---


### B-608 - Quadrature sum decomposes over node-list append

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Quadrature sum decomposes over node-list append |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
In QuadratureUp with finite node-list fold setup, if L = A append B then QuadSum(L,f) classifies with QuadSum(A,f) + QuadSum(B,f).

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`

Rationale:
Existing BOARD covers empty (B-538), singleton (B-575), two-node (B-590), and degree-zero exactness (B-542/B-465). Append decomposition lifts these point-wise readbacks to a fold-level structural identity that subsequent QuadratureUp targets (composite rules, error decompositions) will need. Proof is a list induction reusing the singleton row.

---


### B-609 - AffineVar zero-locus of union is intersection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | AffineVar zero-locus of union is intersection |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
In AffineVarUp with equation-family zero-locus setup, for any equation families F,G and point x, x∈Z(F∪G) iff x∈Z(F) and x∈Z(G).

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`

Rationale:
Extends B-585 (singleton-equation exactness) to the family-coverage level. This is the canonical inversion/coverage bridge for AffineVarUp's equation-family layer and is required for any further variety-intersection or component-level work. Direct unfolding of equation-family membership and zero-locus predicate; no external algebraic geometry.

---

