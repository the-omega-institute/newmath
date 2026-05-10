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
