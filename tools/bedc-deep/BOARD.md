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

### B-513 - ODE local-flow concatenation associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ODE local-flow concatenation associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
If R_{01}, R_{12}, R_{23} are three OdeUp BHist local-flow rows with matching shared endpoints (terminal of R_{ij} classified with initial of R_{jk} in the derivative-time and Banach-state classifiers), then the two grouped composites (R_{01}∘R_{12})∘R_{23} and R_{01}∘(R_{12}∘R_{23}) — built by iterated thm:ode-root-picard-continuation-scope — have endpoint state histories related by the BanachUp classifier ∼_BanachUp.

Local inputs:
- `papers/bedc/parts/concrete_instances/171_ode_namecert_construction.tex`

Rationale:
171_ode_namecert_construction.tex (204 lines, 4 thms) currently caps at the binary thm:ode-local-flow-concatenation-endpoint-determinacy (B-452, line 132). Three-step associativity is the natural next theorem: it requires applying the binary determinacy theorem to two distinct groupings of the three-step composite, then composing the two endpoint-classifier witnesses through ∼_BanachUp transitivity. grep 'three-step\|three.*step.*flow\|associativity.*flow' on the file returns 0 hits; the parallel result at the higher DynSystemUp layer (173_dynsystem line 262 thm:dynsystem-flow-composition-ledger) is binary, not three-step, and DynSystemUp is a different (higher-tower) chapter. BOARD entry B-452 is binary; B-453 sheaf point-germ comparison transitivity is sheaf-specific; no three-step ODE entry exists. Proof: instantiate thm:ode-local-flow-concatenation-endpoint-determinacy twice with appropriate Lipschitz vector-field ledger comparisons (already required to exist by Cont associativity, line 88), compose endpoint witnesses by Banach classifier transitivity. Concrete implication, fits 204-line file.

---

### B-514 - InnerProduct polarization-difference identity row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | InnerProduct polarization-difference identity row |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For carried vector endpoints x,y in the parallelogram norm seed source, the scalar history \|x+_V y\|_I^2 +_K (-_K \|x-_V y\|_I^2) is classifier-equal under sim_K to 2_K cdot_K (langle x,y rangle_I +_K langle y,x rangle_I).

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/parallelogram_norm_seed.tex`
- `papers/bedc/parts/concrete_instances/innerproduct/core_surface.tex`

Rationale:
Companion to the existing parallelogram-identity row (sum form). The chapter records the SUM expansion \|x+y\|^2 + \|x-y\|^2 = 2(\|x\|^2 + \|y\|^2) but not the DIFFERENCE expansion \|x+y\|^2 - \|x-y\|^2 = 2(<x,y> + <y,x>), which is the residue of the same vecspace-linearity rows when subtracted. Diagonal terms cancel and cross terms double — a structural identity that bridges parallelogram seed to inner-product symmetry surface. No existing BOARD or paper coverage for polarization in innerproduct/. Single implication, lands in a small seed file far below cap. Neither this nor B-508 (Pythagorean) covers the difference identity.

---

### B-515 - Singleton edge predicate is a matching

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Singleton edge predicate is a matching |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For a GraphUp carrier G with edge classifier sim_E and a carried edge e_star satisfying Edge_G(e_star), the predicate M_{e_star}(e) := e sim_E e_star is a MatchingEdgeSet_G.

Local inputs:
- `papers/bedc/parts/concrete_instances/212_matching_namecert_construction.tex`

Rationale:
Upper-unit dual to B-479 'Empty edge predicate is a matching'. The empty case gives the lower unit; the singleton case is the smallest non-trivial matching and the canonical building block for finite matching constructions. No-shared-vertex row collapses through classifier symmetry+transitivity since both endpoints of any in-set pair are sim_E e_star. Distinct from B-418 (compatible union closure) which assumes disjoint matchings already exist. Single implication, ~10 lines in a 143-line chapter. Provides the missing seed for any inductive matching construction over GraphUp.

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

### B-517 - Hash collision-freeness is symmetric in the message pair

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Hash collision-freeness is symmetric in the message pair |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For a HashUp certificate H whose message and digest classifiers carry the symmetry fields supplied by their naming-certificate components, CollFreeH_H(x, x_prime) implies CollFreeH_H(x_prime, x).

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`

Rationale:
Negation-form companion to thm:hash-collision-success-symmetric. The chapter records collision-success symmetry and the second-preimage exclusion (B-489) but never the contrapositive transport: that collision-freeness itself is symmetric in the message pair. Lifts cleanly via negation of the existing symmetry: assume CollFreeH(x,x_prime) and HashCollisionSuccess(x_prime,x); apply success-symmetry to derive HashCollisionSuccess(x,x_prime); contradicts CollFreeH. Borderline on parameter-echo since it is a contrapositive of an existing symmetry, but it operates on a separately-defined predicate (CollFreeH not definitionally collapsed onto ¬CollSuccess) so the transport step is a real proof obligation, not pure rewriting. Held novelty at 6, the threshold.

---
