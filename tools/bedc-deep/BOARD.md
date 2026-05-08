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

### B-511 - Independence finite subfamily projection

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Independence finite subfamily projection |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If a finite-family carrier (X_i)_{i in I} carries the IndependenceUp finite factorisation row of def:independence-finite-factorisation-row, then for every FinSetUp-certified subset J ⊆ I the restricted family (X_i)_{i in J} also carries the finite factorisation row.

Local inputs:
- `papers/bedc/parts/concrete_instances/165_independence_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`

Rationale:
165_independence_namecert_construction.tex builds finite-family independence around def:independence-finite-factorisation-row (lines 49-75) and proves stability under reindexing permutations (thm:independence-finite-reindexing-invariance, line 203) and binary measurable-image transport (thm:independence-measurable-image-bridge, line 270). The fundamental subfamily projection — independence of the full family implies independence of any sub-index family — is missing: grep 'subfamily\|sub-index\|index.*restriction\|restrict.*independence\|partial.*independence' on the file returns 0 matches. BOARD already covers Distribution↑ pushforward sigma-additivity / inclusion-exclusion (B-475, B-503/506) and B-499 finite-family measurable-image independence — none addresses index-restriction. The proof: take an arbitrary cylinder over J, complete it to a cylinder over I by inserting the total-event B_i = T_i for i ∉ J (using ProbSpaceUp normalization mu(Omega) ~ 1_R from thm:probspace-total-event-normalization-row at 162_probspace line 130), apply the full-family factorisation, and absorb the unit-marginals via finite RealUp product fold. Lands in 362-line file, well below cap; concrete prerequisite for downstream CondExp/Markov chain reasoning.

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
