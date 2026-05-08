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

### B-519 - LPDuality dual feasibility binary convex closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LPDuality dual feasibility binary convex closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 8/10 |

Problem:
In a finite $\LPDualityUp$ ordered-field row, if $y$ and $y'$ are $\mathsf{DuFeas}_{A,b,c}$ and $a,b$ are scalar coefficients with $\mathsf{NonNeg}_F(a)$, $\mathsf{NonNeg}_F(b)$, and $(a +_F b) \sim_F 1_F$, then the componentwise sum $\eta_i := a \cdot_F y_i +_F b \cdot_F y_i'$ is $\mathsf{DuFeas}_{A,b,c}$.

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
B-516 `LPDuality primal feasibility binary convex closure` is on the BOARD pending list as the primal-side companion of weak-duality (B-429), complementary slackness (B-447), and weak-duality-equality optimality (B-444). Inspecting 213_lpduality_namecert_construction.tex:50-69 confirms the chapter exposes a separate `\mathsf{DuFeas}_{A,b,c}` predicate (dual feasibility, with $c_j \preceq_F \beta_j(y)$ rows) that has identical convex-closure structure: nonneg coefficients sum to one, finite-sum monotonicity row inherits, and dual constraint $c_j \preceq_F \beta_j(\eta)$ falls out of left/right multiplication monotonicity rows already named in the feasibility row at lines 18-36. The dual side is a structural mirror that B-516 deliberately omits; by symmetry of LP duality this is the natural complement, not a duplicate. File is 276 lines, plenty of room.

---

### B-522 - Banach zero bounded operator left-composition annihilation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Banach zero bounded operator left-composition annihilation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If $T:H_1\to H_2$ is a carried $\BanachUp$ bounded linear operator and $0_{H_0,H_1}$ is the zero bounded linear operator carried by \autoref{thm:banach-zero-bounded-linear-operator-carrier}, then the composite $T\circ 0_{H_0,H_1}$ is classifier-equal to $0_{H_0,H_2}$ in the $\BanachUp$ bounded-operator classifier on $(H_0,H_2)$.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex`

Rationale:
Banach completed targets are B-480 (zero bounded-linear operator carrier), B-481 (identity composition units), Banach bounded operator composition closure, and B-491 (bound weakening). The chapter has B-481 (identity ∘ T = T) but is missing the dual fact for the zero operator: composing with zero on either side gives zero. This is the standard 'zero is absorbing under composition' law that complements identity-as-unit. File bounded_linear_operator_composition.tex is 366 lines (well below cap), and it already proves bounded composition closure at line 134 and identity units at line 303 — the zero-absorption proof reuses the same finite-prefix Lipschitz tracking against the zero Cauchy modulus.

---

### B-523 - Hash collision-success is irreflexive on the message

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Hash collision-success is irreflexive on the message |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For any HashUp certificate H whose message classifier carries the naming-certificate reflexivity field, and for every history x, HashCollisionSuccess_H(x, x) implies bot.

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`

Rationale:
Clean diagonal-impossibility companion to the existing hash-collision family (B-517 symmetry, B-489 second-preimage exclusion, B-464 reversed second-preimage, B-373 transcript symmetry, B-367 collision-success symmetry, B-361 second-preimage induces collision). None of those treat the reflexive case. The chapter (220_hash, 193 lines) defines HashCollisionSuccess via a `not sigma_H(x,x')` distinction premise, so reflexivity of sigma_H gives an immediate obstruction proof — concrete obstruction target, not a parameter echo. Lands as ~10 lines after thm:hash-collision-transcript-symmetry without hub or line-cap risk.

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

### B-525 - LPDuality dual feasibility binary convex closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | LPDuality dual feasibility binary convex closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
In a finite LPDualityUp ordered-field row, if y and y' satisfy DuFeas_{A,b,c} and a,b are nonneg scalars with (a+_F b) sim_F 1_F, then mu_i := a *_F y_i +_F b *_F y'_i also satisfies DuFeas_{A,b,c}.

Local inputs:
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
Symmetric dual-side companion to the in-progress B-516 (LPDuality PRIMAL feasibility binary convex closure). LP duality theory is incomplete without symmetric closure on both feasibility cones; the chapter already has weak duality (thm 72), weak-duality-equality optimality (cor 139), and complementary slackness (thm 191), but no convex closure on either side. The dual case is not redundant with the primal — different inequality direction (c_j preceq_F beta_j(y)) and uses NonNeg multiplicative monotonicity in the opposite orientation. Concrete closure target, not parameter echo. File 276 lines, safe.

---

### B-526 - ConvexSet linear preimage carries the binary affine-combination row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ConvexSet linear preimage carries the binary affine-combination row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If f: V→W is a carried LinearMapUp and D is a convex carrier in W satisfying the binary affine-combination row of def:convexset-binary-affine-combination-row, then the source-side preimage carrier f^{-1}(D)(x) := D(f(x)) on the source vector carrier C_V satisfies the same binary nonneg unit-sum affine-combination closure row over the same FieldUp scalar source.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/23_linearmap_namecert_construction.tex`

Rationale:
186_convexset already proves the IMAGE direction in thm:convexset-linear-image-affine-combination-closure (186:249-312) and thm:convexset-linear-image-finite-affine-spine-closure (186:314-346) via def:convexset-linear-image-carrier (186:238). The dual PREIMAGE direction is structurally simpler (no codomain-classifier transport needed; just push the f-output condition through linearity) and is genuinely missing. `Grep -rn 'preimage|f^{-1}.*convex|convex.*preimage' papers/bedc/parts/` returns 0 hits across the entire parts/ tree, and there is no `BEDC.Derived.ConvexSetUp.*Preimage` Lean target. File is 357 lines, well below the 760 cap, and follows the same chapter as the image case so the local style cues already exist.

---

### B-527 - Independence empty index family carries the finite factorisation row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Independence empty index family carries the finite factorisation row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a finite-family carrier R for IndependenceUp in the sense of def:independence-finite-family-carrier has empty FinSetUp index carrier I = ∅, then R satisfies the finite factorisation row of def:independence-finite-factorisation-row: for the unique empty event-family B, μ_X^J(Cyl_X(B)) ~_R Π_R(MargSp_X(B)) holds, both endpoints being the empty-product unit 1_R.

Local inputs:
- `papers/bedc/parts/concrete_instances/165_independence_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`

Rationale:
165_independence has 11 theorems including B-477 (finite reindexing invariance), B-499 (measurable-image bridge), and B-511 (subfamily projection), but `grep -rn 'empty.*independence|empty.*indep.*finite|empty.*family.*independent' papers/bedc/parts/` returns 0 hits about IndependenceUp empty-family. (180 hits for matroid-empty are different concept.) The empty-index degenerate case is conceptually distinct from B-511 because it does not require an ambient-family hypothesis: it is structural—the joint pushforward of an empty-tuple map onto the singleton empty-product target is the total mass 1_R by ProbSpace total-mass row (thm:probspace-total-event-normalization-row, 162:130), and the empty real-product fold is 1_R by the finite-fold definitions. Closes the foundational degenerate case that the existing theorems all assume to be discharged. File at 362 lines.

---
