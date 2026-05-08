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

### B-516 - LPDuality primal feasibility binary convex closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | LPDuality primal feasibility binary convex closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
In a finite LPDualityUp ordered-field row, if x and x_prime are PrFeas_{A,b}, and a,b are scalar coefficients with NonNeg_F(a), NonNeg_F(b), and (a +_F b) sim_F 1_F, then the componentwise sum lambda_j := a cdot_F x_j +_F b cdot_F x_prime_j satisfies PrFeas_{A,b}(lambda).

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
Structural shape result for LPDualityUp's feasible set — convex combination closure. Existing chapter theorems (B-444 weak duality, B-447 complementary slackness, B-429 feasible weak duality) all operate on point feasible witnesses; none records that the primal feasible set is closed under convex combinations, which is the property that gives LPDualityUp its convex-polytope identity downstream. Proof reduces to nonneg-scalar monotonicity + finite-sum monotonicity + finite distributivity, all already exposed in def:lpduality-finite-ordered-field-feasibility-row. Distinct closure target, not parameter echo of existing duality results.

---

### B-518 - AbelianCat zero morphism left-absorbing under composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AbelianCat zero morphism left-absorbing under composition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For carried hom $f \in \mathcal{H}(X,A)$ in an $\AbelianCatUp$ additive kernel-cokernel carrier, the displayed composite $0_{A,B}\circ f$ is classified by $\sim_{X,B}$ with the displayed zero morphism $0_{X,B}$.

Local inputs:
- `papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex`

Rationale:
AbelianCat is a 433-line chapter with 10 theorems but only B-423 (`AbelianCat hom zero morphism uniqueness`, line 380) and B-437 (kernel/cokernel factor uniqueness) completed. The zero-morphism API in 154_abeliancat_namecert_construction.tex:380-421 establishes that $0_{A,B}$ is the unique left/right additive identity but never asserts the corresponding composition-annihilation row that makes zero morphisms `compose to zero'. This is the foundational fact that turns the existing zero-biproduct surface (\autoref{thm:abeliancat-additive-zero-biproduct-obligation} at line 79) into a usable abelian-category obligation. Single implication, concrete, in chapter scope. No abstract carrier transport — this is content over the displayed hom carriers. No collision with BOARD index B-407..B-516 or completed list.

---

### B-524 - RandomVar countable preimage intersection exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | RandomVar countable preimage intersection exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 7/10 |

Problem:
If X:S->T is a carried RandomVarUp map and B_n in A_T is a target measurable-event sequence with intersection event I_T, then each preimage A_n := X^{-1}(B_n) and A_I := X^{-1}(I_T) lies in A_S, and A_I is source-classifier-equal to the source measurable countable intersection of A_bullet.

Local inputs:
- `papers/bedc/parts/concrete_instances/randomvar/terminal_and_countable_preimage.tex`

Rationale:
Strict dual companion to B-474 (countable preimage UNION exactness), the only sigma-algebra closure case missing from the RandomVar preimage exactness suite (B-474 union, B-419 preimage union, B-456 empty preimage, B-455 total preimage, B-439 complement, B-434 relative-difference, plus binary intersection in countable_and_intersection.tex). The scoped-closure package thm:randomvar-scoped-closure-package currently only mentions countable union; a probability-theory referee would call this out. Concrete sigma-algebra closure, not a parameter transport — proof mirrors the union proof with exists -> forall. File 171 lines, safe landing.

---

### B-537 - DirichletUnit inherited unit-product closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | DirichletUnit inherited unit-product closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
If two accepted DirichletUnitUp unit rows over the same RingOfIntegersUp and AbGroupUp dependency packets carry their inverse/unit-product witnesses, then the inherited AbGroupUp operation endpoint is again a visible DirichletUnitUp unit row with the shared Pkg and Cont provenance.

Local inputs:
- `papers/bedc/parts/concrete_instances/149_dirichletunit_namecert_construction.tex`

Rationale:
DirichletUnitUp is a number-theoretic surface with no active or completed BOARD target found in the target/state scans, while the body file is small and concrete. The carrier explicitly lists a visible unit row u and an inverse/unit-product witness row iota at papers/bedc/parts/concrete_instances/149_dirichletunit_namecert_construction.tex:11-15, and the public abelian-group dependency is restricted to unit rows accepted by the RingOfIntegersUp dependency at papers/bedc/parts/concrete_instances/149_dirichletunit_namecert_construction.tex:55-64. The later AbGroup projection exposes operation, inverse, identity, and classifier rows at papers/bedc/parts/concrete_instances/149_dirichletunit_namecert_construction.tex:114-135, but there is no theorem in the file asserting that the inherited product of two visible unit rows is again a DirichletUnitUp visible unit row. This is a concrete missing closure law, not a marker/status update or abstract classifier transport.

---


### B-538 - Quadrature empty-node sum is zero

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quadrature empty-node sum is zero |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For a finite weighted QuadratureUp rule Q=(xs,alpha,omega,I_Q), if the FinSetUp node spine xs is empty, then for every finite polynomial-code spine p the quadrature fold QSum_Q(p) is scalar-classifier-equal to 0_R.

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`

Rationale:
QuadratureUp has completed coverage for the exactness-degree classifier, but that coverage is concentrated on degree weakening, reflexivity, transitivity, and preorder rows: see the definitions of QSum_Q and DegBoundLe at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:21-66 and the completed theorem suite at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:105-240. The concrete rule-level fold itself is defined as a finite additive fold over Pos(xs) at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:27-31, while the existing ledger theorem only states that this is the carried exactness surface at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:90-103. The empty-node boundary is not one of B-428, B-451, or B-465 and is a small concrete implication about the actual quadrature sum rather than another degree-classifier law.

---


### B-539 - SpectralSeq boundary rows enter successor cycles

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | SpectralSeq boundary rows enter successor cycles |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
For a SpectralSeqUp page carrier whose differential ledger includes the displayed square-zero row for d_r, any boundary representative read through the homology-page readback h is classified as a cycle row on the successor-page surface.

Local inputs:
- `papers/bedc/parts/concrete_instances/156_spectralseq_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/76_homology_namecert_construction.tex`

Rationale:
SpectralSeqUp is a thin homological interface with only a carrier, classifier, obligation surface, differential-ledger stability, and convergence boundary; its carrier says h identifies each successor page with the HomologyUp cycle row of d_r modulo the displayed boundary row at papers/bedc/parts/concrete_instances/156_spectralseq_namecert_construction.tex:24-26, and the obligation surface lists differential-square rows plus homology-page readback rows at papers/bedc/parts/concrete_instances/156_spectralseq_namecert_construction.tex:60-68. The existing stability theorem preserves readback under classifier transport at papers/bedc/parts/concrete_instances/156_spectralseq_namecert_construction.tex:86-110, but it does not instantiate the concrete HomologyUp theorem that square-zero differentials send boundary carriers into cycle carriers. That substrate theorem is already present at papers/bedc/parts/concrete_instances/76_homology_namecert_construction.tex:53-67, so this candidate is a missing middle step between the spectral-sequence page surface and the homology boundary-cycle row rather than a new general theory of spectral sequences.

---

