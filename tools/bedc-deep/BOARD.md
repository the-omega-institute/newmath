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
