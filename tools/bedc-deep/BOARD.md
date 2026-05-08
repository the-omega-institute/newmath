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

### B-540 - LPDuality optimal face convex closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | LPDuality optimal face convex closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
In a finite LPDualityUp ordered-field row, if x and x_prime are primal feasible, both have primal objective classifier-equal to the same certified optimal scalar tau, and alpha,beta are nonnegative with alpha +_F beta sim_F 1_F, then the componentwise affine mixture lambda_j := alpha *_F x_j +_F beta *_F x_prime_j is primal feasible and has primal objective classifier-equal to tau.

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
This is a distinct structural strengthening of the existing LPDuality surface: existing BOARD entries cover primal and dual feasibility convex closure, while the paper already has weak duality and equality-implies-optimality rows. The proposed target combines feasibility convexity with objective affine readback to close the optimal primal face under binary affine combinations, without introducing a new LP interface or an external assumption.

---

### B-542 - Quadrature degree-zero exactness iff weight sum

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Quadrature degree-zero exactness iff weight sum |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
In a finite weighted QuadratureUp rule Q, if one_Q is the constant-one polynomial code and W_Q is the finite fold of the node weights, then QExact_Q(one_Q) holds iff W_Q is scalar-classifier-equal to the integral endpoint I_Q(one_Q).

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`

Rationale:
The Quadrature surface has exactness-degree weakening, degree-bound preorder rows, and an active empty-node sum target, but no base readback for degree-zero exactness. This candidate is a small concrete readback theorem connecting the constant polynomial row to the node-weight budget, and it lands safely in the existing finite weighted QuadratureUp chapter without duplicating current BOARD titles or paper labels.

---
