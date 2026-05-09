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

### B-572 - ConvexSet pointwise (Minkowski) sum closes under the binary affine combination row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ConvexSet pointwise (Minkowski) sum closes under the binary affine combination row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If C and D are ConvexSetUp carriers over the same VecSpaceUp source V each supplying the binary affine-combination row, then the pointwise sum C+_*D := {z : ∃c,d, C(c) ∧ D(d) ∧ z ~_V c +_V d} also satisfies the binary affine-combination row of `def:convexset-binary-affine-combination-row`.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`

Rationale:
The chapter has intersection (`thm:convexset-pointwise-intersection-affine-combination-closure` at 186_convexset_namecert_construction.tex:207), linear image (`thm:convexset-linear-image-affine-combination-closure`:250), and linear preimage (`thm:convexset-linear-preimage-affine-combination-closure`:369) closures, but NOT the Minkowski (pointwise) sum closure. Standard textbook (Rockafellar Convex Analysis Ch.II §3.1: 'if C, D are convex then C+D is convex'). Proof uses `def:convexset-binary-affine-combination-row` separately on C and D, then VecSpaceUp distributivity and middle-four interchange (`thm:abgroup-middle-four-interchange`) to regroup a(c1+d1) + b(c2+d2) as (ac1+bc2) + (ad1+bd2). All three pieces exist. File is 431 lines (room remains). Closes in 2-3 rounds. Not a parameter-transport echo: it constructs a new convex set from two and verifies the binary affine row, an explicit closure law.

---

### B-573 - InnerProduct norm-squared of scalar action factors as scalar self-product times norm-squared

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct norm-squared of scalar action factors as scalar self-product times norm-squared |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For every carried scalar r and carried vector x in an InnerProductUp BHist source, the norm-squared endpoint ||r ·_V x||²_I is classified by the retained scalar classifier with (r ·_K conj_K(r)) ·_K ||x||²_I.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/norm_metric_seed.tex`

Rationale:
The chapter proves `thm:innerproduct-norm-squared-carrier-row` (carrier transport, 25_polynomial_literal_addtrim_eval would not be, this is innerproduct/norm_metric_seed.tex:25) and the linearity row `thm:innerproduct-vecspace-linearity-row` (innerproduct/core_surface.tex:121) handles both additive and scalar-action arguments with the conjugate handling promised on the conjugate-linear side. Polarization-difference and parallelogram are in the parallelogram seed. But the explicit norm-scaling identity ||r·x||²_I ~ (r·conj(r))·||x||²_I is missing — standard textbook (Folland Real Analysis Ch.5 §5.5, Conway Functional Analysis I §I.1.5: 'inner product is conjugate-bilinear, hence ||rx||² = |r|²||x||²'). Proof: apply linearity at left slot to extract r, then linearity at right slot with conjugation to extract conj(r), then scalar associativity. File norm_metric_seed.tex is only 101 lines. Closes in 2-3 rounds; the only nontrivial step is checking the conjugate-linearity clause of the existing linearity row at the right argument, which the row explicitly promises (core_surface.tex:140, 'the conjugate argument handled by the displayed conjugation row when the source uses that side as the conjugate-linear argument').

---
