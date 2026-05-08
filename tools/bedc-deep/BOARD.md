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

### B-549 - LPDuality optimal dual face binary convex closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LPDuality optimal dual face binary convex closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If y, y':I->F are dual feasible witnesses with DuObj_b(y)~_F tau and DuObj_b(y')~_F tau, alpha,beta are nonnegative scalars with alpha+_F beta ~_F 1_F, then the componentwise mixture mu_i := alpha*y_i +_F beta*y'_i satisfies DuFeas_{A,b,c}(mu) and DuObj_b(mu) ~_F tau.

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
File 213_lpduality_namecert_construction.tex (656 lines) carries DuFeas (line 59) and DuObj (line 68), thm:lpduality-dual-feasibility-binary-convex-closure (line 279), and the symmetric thm:lpduality-primal-feasibility-binary-convex-closure (line 400). At line 552 it proves thm:lpduality-optimal-primal-face-binary-convex-closure: a binary mixture of two primal-feasible vectors with the same primal objective tau stays primal-feasible AND keeps the same primal objective tau. The dual-side analog (B-540 'LPDuality optimal face convex closure' was a closely-related but DIFFERENT claim about optimal-face primal closure under fixed coefficient sums; the optimal DUAL face closure is not in the BOARD title index). Required ingredients all already present: lem:lpduality-primal-objective-binary-affine-readback (line 517) is the primal-side affine readback used in the primal-face proof; the dual proof needs an analogous DuObj binary-affine readback, which the chapter sketches but does not state. Concrete clean implication; proof mirrors lines 552-655 with primal-dual swap. File at 656 lines — adding ~80 lines of theorem+proof keeps it under 800.

---

