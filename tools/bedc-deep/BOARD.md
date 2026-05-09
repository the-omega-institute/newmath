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

### B-583 - CliffordUp polarization identity uv + vu ~ q(u+v) - q(u) - q(v)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CliffordUp polarization identity uv + vu ~ q(u+v) - q(u) - q(v) |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For accepted vector histories u,v in the shared VecSpaceUp source, the Clifford classifier identifies u*v + v*u with q(u+v) - q(u) - q(v) via the displayed quadratic-relation row applied to u+v together with bilinearity transport from BilinFormUp.

Local inputs:
- `papers/bedc/parts/concrete_instances/125_clifford_namecert_construction.tex`

Rationale:
125_clifford has the diagonal quadratic-relation v*v ~ q(v)*1 and product-stability/confluence rows, but the universal symmetric polarization formula relating two distinct vectors is not derived. Polarization is the unique fact that distinguishes Clifford from a free tensor algebra and what downstream Spin/Pin certificates need to anchor double-cover constructions. Polarization shows up only in commring/innerproduct chapters elsewhere, never in Clifford. Frontier algebra capstone.

---

### B-587 - PolynomialUp raw multiplication left distributivity over raw addition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | PolynomialUp raw multiplication left distributivity over raw addition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For accepted spines x, y, z over a CommRingUp scalar source, the raw Cauchy product rmul_R(x, radd_R(y,z)) classifies in the polynomial classifier with radd_R(rmul_R(x,y), rmul_R(x,z)).

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_multiplication.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex`

Rationale:
B-579 records ONLY the right distributivity row (`(x+y)*z ~ x*z + y*z`) for raw polynomial multiplication; the dual `x*(y+z) ~ x*y + x*z` is not in BOARD nor in `25_polynomial_literal_multiplication.tex` (the file lists Cauchy coefficient formula at line 19, associativity at line 55, and singleton evaluation at line 77, with no left-distributivity row). Both polynomial-multiplication zero-absorptions (left at line 202, right at line 244) appear in the algebra sibling, so the symmetric pair is published for zero-absorption but is asymmetric for distributivity. The file is 103 lines, far below the 800 cap, and a clean coefficient-fold proof is available via `lem:scalar-product-distributes-across-finite-additive-folds` already used in associativity (line 50).

---

