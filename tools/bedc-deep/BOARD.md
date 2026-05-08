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

### B-529 - HopfAlgUp antipode uniqueness from convolution-inverse witnesses

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | HopfAlgUp antipode uniqueness from convolution-inverse witnesses |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For a HopfAlgUp BHist bialgebra carrier and two antipode rows s, s' that both witness the convolution-inverse obligation (both ConvLeft and ConvRight ledgers compose to the unit-counit endpoint with each), the two antipode rows are classifier-equivalent: hsame(s, s').

Local inputs:
- `papers/bedc/parts/concrete_instances/158_hopfalg_namecert_construction.tex`

Rationale:
Frontier first closure on a 92-line chapter that currently has only carrier definition, classifier, tensor-product stability, antipode obligation, and namecert obligation — no closure theorem at all. Antipode uniqueness is the canonical first theorem any reader expects in a HopfAlg surface and is the principal property that distinguishes Hopf algebras from bialgebras. Concrete uniqueness target (not parameter-echo). Large landing headroom. Likely oracle route because convolution-associativity needs careful BHist-level statement.

---

### B-531 - AbelianCatUp zero-morphism right-absorbing under composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AbelianCatUp zero-morphism right-absorbing under composition |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For carried homs g ∈ H(A, B) and the displayed zero morphism 0_{X,A} ∈ H(X, A) in an AbelianCatUp additive kernel-cokernel carrier, the displayed composite g ∘ 0_{X,A} is classified by ~_{X,B} with the displayed zero morphism 0_{X,B}.

Local inputs:
- `papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex`

Rationale:
Symmetric companion to in-progress B-518 (left-absorbing 0∘f). Not a duplicate: opposite composition slot, separate theorem statement. The two together complete the 'two-sided absorbing' shape that any reader expects together. Proof mirrors B-518 via biproduct hom additivity (line 211) and zero morphism uniqueness (B-423). File safe at 433 lines. Codex_close in 1-2 rounds once B-518 lands.

---

### B-532 - Banach bounded-linear-operator pointwise sum closure with norm subadditivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Banach bounded-linear-operator pointwise sum closure with norm subadditivity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For two displayed bounded-linear-operator naming certificates T, S over the same Banach source, the pointwise sum T + S (defined by the addition row of the target Banach AbGroupUp on each input endpoint) is itself a bounded linear operator, and its operator-bound row is classified ≤_R the scalar sum of the displayed bounds for T and S under the RealAlgOrder additive order row.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex`
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`

Rationale:
Frontier first closure: chapter has identity (B-481), zero (B-480), composition (B-375), and Lipschitz constant composition, but no additive closure on bounded-linear operators. Without it the bounded-operator class is not stated as a Banach-AbGroupUp object and downstream OperatorIdealUp / FunctionalAnalysisUp consumers must reconstruct ad-hoc. Companion-of-canon to the operator-norm composition Lipschitz row at line 24. File safe at 451 lines. Likely oracle for the bound transport.

---

### B-533 - Measure ternary-union subadditivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Measure ternary-union subadditivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
For a MeasureUp carrier with R-valued measure mu and three measurable events A, B, C, if U_BC is the displayed binary union of B and C and U is the displayed binary union of A and U_BC, and if the certificate supplies binary-union subadditivity, finite disjoint-union additivity, the nonnegative measure-value row, and the RealAlgOrder addition-monotonicity row, then mu(U) le_R mu(A) + mu(B) + mu(C).

Local inputs:
- `papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex`

Rationale:
The binary case (B-433) is proved at papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex:199 thm:measure-binary-union-subadditivity (mu(A cup B) le_R mu(A) + mu(B)). Grep across papers/bedc/parts for `measure-ternary|measure-three-union|measure-finite-union-subadditivity` returned zero matches; only the existing binary form and the unrelated `measure-finite-disjoint-union-additivity` (which requires disjointness) appear. The proof composes binary subadditivity twice -- once on (B, C) yielding mu(U_BC) le mu(B) + mu(C), then on (A, U_BC) yielding mu(U) le mu(A) + mu(U_BC) -- and chains by addition monotonicity. Concrete inequality on existing measure values, not a parameter echo. File currently 248 lines, fits append. Lands in the `measure/` child directory, not a hub.

---

### B-534 - AbelianCat hom additive inverse uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AbelianCat hom additive inverse uniqueness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For carried hom morphisms $f, u, v \in \mathcal{H}(A,B)$ in an $\AbelianCatUp$ additive kernel-cokernel carrier, if $u +_{A,B} f \sim_{A,B} 0_{A,B}$, $f +_{A,B} u \sim_{A,B} 0_{A,B}$, $v +_{A,B} f \sim_{A,B} 0_{A,B}$, and $f +_{A,B} v \sim_{A,B} 0_{A,B}$, then $u \sim_{A,B} v$.

Local inputs:
- `papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex`

Rationale:
Concrete two-sided-inverse uniqueness for the abelian-group hom row of an AbelianCatUp carrier, distinct from the existing zero-morphism uniqueness at B-423 (thm:abeliancat-hom-zero-morphism-uniqueness) and from the zero composition-absorption pair B-518/B-531. The proof routes through the same prop:abgroup-forgets-group-certificate / prop:group-forgets-monoid-certificate reduction the chapter already uses, then invokes group-inverse uniqueness rather than monoid-identity uniqueness, so the lemma fills a known companion gap in the AbelianCat additivity surface. The landing file 154_abeliancat_namecert_construction.tex is well below the line cap and is the canonical site for hom-row uniqueness statements; the new theorem lands directly after thm:abeliancat-hom-zero-morphism-uniqueness without needing a hub split.

---


### B-535 - Hash collision-success induces same-direction second-preimage success

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Hash collision-success induces same-direction second-preimage success |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For a $\HashUp$ certificate $\mathcal{H}$ whose digest classifier carries the $\NameCert_{\FinSetUp}$ symmetry field, every successful collision transcript at message pair $(x, x')$ induces a successful second-preimage transcript with base message $x$ and returned message $x'$ over the same hash-evaluation rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`

Rationale:
Same-direction sibling of B-464 (collision-success $\Rightarrow$ reversed second-preimage). Existing surface gives collision $\Rightarrow$ second-preimage at $(x',x)$ and the reverse implication second-preimage at $(x,x') \Rightarrow$ collision; the same-direction collision $\Rightarrow$ second-preimage at $(x,x')$ is genuinely missing and does not fall out of either direction without an extra digest-classifier symmetry pass on $\rho(d,d')$. With B-517 (collision-freeness symmetry) and thm:hash-collision-transcript-symmetry already in place, the proof composes B-464 with digest-classifier symmetry in a small but distinct way, and the result is consumed downstream whenever Hash chapters need a same-direction second-preimage witness instead of the reversed pairing. Landing site 220_hash_namecert_construction.tex is safely below the line cap and already hosts the related transcript-symmetry block, so the new theorem lands cleanly after thm:hash-collision-transcript-symmetry.

---

