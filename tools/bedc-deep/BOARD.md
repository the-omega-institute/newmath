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

### B-574 - LambdaCalc alpha classifier transitivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LambdaCalc alpha classifier transitivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If two accepted alpha-classifier rows relate $(s,t)$ and $(t,u)$ over accepted $\LambdaCalcUp$ term packets sharing the displayed $\TreeUp$ syntax row and $\NatUp$ binder ledger, then the composed alpha-classifier row relating $(s,u)$ is also accepted, with reversed and concatenated carried $\hsame$ rows on the $\TreeUp$ skeletons and the $\NatUp$ binder indices.

Local inputs:
- `papers/bedc/parts/concrete_instances/178_lambdacalc_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/lambdacalc/root_frontier.tex`

Rationale:
The lambdacalc chapter currently exposes alpha-classifier reflexivity at `papers/bedc/parts/concrete_instances/178_lambdacalc_namecert_construction.tex:244-272` (`thm:lambdacalc-carrier-reflexive`) and alpha-classifier symmetry at lines 274-302 (`thm:lambdacalc-alpha-classifier-symmetric`), but no transitivity row anywhere in the chapter or its split sub-files (`lambdacalc/root_normal_form_boundary.tex`, `root_frontier.tex`, `namecert_public_boundary.tex`). Among the 25 theorems in the parent file and 17 in its sub-files, no completed BOARD target (search across `b-*_lambdacalc_*` returns only the parent chapter not yet probed by bedc-deep) covers transitivity. This is a textbook structural blindspot: equivalence-classifier predicates uniformly receive refl/sym/trans, and lambdacalc has the first two but the third is a simple compose-the-witnesses argument. Loning's parallel pipeline has not touched it either. The parent file is at 735/800 lines so the new theorem can land in `lambdacalc/root_frontier.tex` (293 lines, ample room) as a sibling body file.

---


### B-575 - Quadrature singleton-node sum equals weight times integrand evaluation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quadrature singleton-node sum equals weight times integrand evaluation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If $Q=(xs,\alpha,\omega,\mathcal{I}_Q)$ is a finite weighted $\QuadratureUp$ rule over the scalar carrier $R$ in the sense of `def:quadrature-finite-weighted-exactness-degree`, and the $\FinSetUp$ node spine $xs$ enumerates exactly one position $i_0$, then for every finite polynomial-code spine $p:\mathsf{ListCarrier}(R)$, $\mathsf{QSum}_Q(p)\sim_R \omega_{i_0}\cdot \mathsf{Eval}_{\alpha_{i_0},R}(p)$.

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`

Rationale:
The Quadrature chapter (`papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`, 291 lines) handles the empty-node-spine case in `thm:quadrature-empty-node-sum-zero` (B-538), the degree-zero exactness/weight-sum equivalence in B-542, and degree-bound preorder (transitivity B-? line 173, reflexivity B-? line 204, weakening line 124, equivalence stability line 149). The singleton-node case — the simplest non-empty quadrature rule — has no companion theorem and is a clean direct unfold of `\mathsf{QSum}_Q(p)` using the singleton clause of `def:finite-additive-scalar-fold` and `lem:quadrature-empty-position-fold-zero` (already present at line 469). It mirrors the existing empty-node closure-status proof and gives downstream numerical-analysis chapters the n=1 base case for inductive arguments over node count.

---


### B-576 - Banach scalar-action of bounded operator distributes over composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Banach scalar-action of bounded operator distributes over composition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If $T:H_0\to H_1$ is a carried $\BanachBLOp$ row with bound $L_T:\RealUp$, $S:H_1\to H_2$ is a carried $\BanachBLOp$ row with bound $L_S:\RealUp$, and $c:\RealUp$ is a carried scalar with $\NonNeg_{\RealUp}(c)$, then the composite $S\circ(c\cdot T)$ is a carried $\BanachBLOp$ row from $H_0$ to $H_2$ with bound $c\cdot L_T\cdot L_S$ and is $\BanachBLOp$-classifier equal to $c\cdot(S\circ T)$ over the same source/target Banach carriers.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex`

Rationale:
The Banach BLO sub-directory has thoroughly developed composition algebra: associativity (line 231), identity units (B-481 line 303), left-zero annihilation (B-522 line 368), right-zero annihilation (B-569 in flight, line 453), composition-Lipschitz (line 24), composition-Cauchy preservation (line 60). The companion file `bounded_linear_operator_obligations.tex` adds scalar-multiple bound (B-541, line 398) and pointwise sum closure (B-532, line 223). What is conspicuously absent is the scalar-action × composition interaction `(c\cdot T)\circ S` or `S\circ(c\cdot T)` — the standard `\mathcal{L}(H_1,H_2)$-bimodule structure over scalars. With both ingredients on hand (scalar-multiple bound and composition closure), this is a direct ledger composition that closes the bilinearity-of-composition gap. File at 514/800 lines has ~280 lines of room.

---


### B-577 - RandomVar preimage symmetric-difference exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RandomVar preimage symmetric-difference exactness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For a carried $\RandomVarUp$ measurable map $f:\Omega\to\Omega'$ and target events $A,B\in\mathcal{A}'$ with classifier-stable measurable preimages and difference rows, the preimage of the symmetric difference $A\triangle B := (A\setminus B)\cup(B\setminus A)$ is classifier-equal to the symmetric difference of the preimages: $f^{-1}(A\triangle B)\sim f^{-1}(A)\triangle f^{-1}(B)$ in the source $\sigma$-algebra.

Local inputs:
- `papers/bedc/parts/concrete_instances/randomvar/preimage_exactness.tex`

Rationale:
The randomvar chapter has expanded its preimage-exactness palette substantially: union exactness (B-419), relative-difference exactness (B-434, file line 60), complement-and-relative-difference exactness (B-439, line 113), empty-event exactness (B-456, line 184), countable union exactness (B-474), countable intersection exactness (B-524), disjoint binary union exactness (line 13). The symmetric-difference case is the natural composition of two of those rows (relative difference applied twice and then unioned) but has no dedicated theorem. It is the standard structural row that downstream measure-theoretic preimage manipulation expects, and the proof factors directly through the existing union (B-419) and relative-difference (B-434) theorems. File `randomvar/preimage_exactness.tex` at 220 lines has room.

---

