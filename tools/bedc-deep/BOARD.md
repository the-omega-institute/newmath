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

### B-506 - Distribution pushforward inclusion-exclusion identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Distribution pushforward inclusion-exclusion identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For a carried RandomVar X:S\to T and target measurable events B,C\in\mathcal A_T, \mu_X(B\cup C)+\mu_X(B\cap C)\sim_R\mu_X(B)+\mu_X(C).

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`

Rationale:
Distinct companion to candidate 1. Existing BOARD coverage on Distribution↑ pushforward is sigma/finite/disjoint additive (B-475, B-438, B-390) and monotone events (B-462, B-466, B-458) — no entry handles the general two-event overlap case via X^{-1} commutation with union/intersection. The proof transports the source-side ProbSpace inclusion-exclusion (candidate 1) through the existing pushforward row (thm:distribution-pushforward-row) using preimage-commutation lemmas already in the chapter. Lands in 164_distribution_namecert_construction.tex — at 749 lines this is near cap, but the new theorem can land in an obvious sibling file under concrete_instances/distribution/ to honor the split-out discipline rather than landing in the hub.

---

### B-507 - Halting predicate exists iff meta-loop closes at certificate stratum

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Halting predicate exists iff meta-loop closes at certificate stratum |
| Layer | capstones |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 9/10 |

Problem:
There exists a halting predicate \NameCert_H over the carrier of all naming certificates if and only if there exists a \NameCert-level decision procedure indexed by the certificate-of-certificates carrier.

Local inputs:
- `papers/bedc/parts/capstones/halting_as_form_of_distinction_limit.tex`

Rationale:
Genuine missing dual. halting_as_form_of_distinction_limit.tex packages the forward direction (thm:halting-meta-loop-closure) but not the converse, even though the proof sketch already cites the equivalence. Filling the gap aligns the chapter with the parallel iffs in three_axioms_one_closure.tex (Choice/Quot.sound/propext stratum closures), which are all packaged as full equivalences. The chapter is 56 lines, safely below cap, and the converse is a one-step re-interpretation. No BOARD entry covers halting predicate existence dualities. Concrete biconditional, fits capstones-stratum surface, not a parameter echo.

---

### B-508 - InnerProduct Pythagorean theorem

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct Pythagorean theorem |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 6/10 |

Problem:
For an $\InnerProductUp$ BHist source, if $x \perp_I y$ for carried vector endpoints $x,y:C_V$, then the diagonal scalar endpoints satisfy $\|x+_V y\|_I^2 \sim_{\mathbb{K}} \|x\|_I^2 +_{\mathbb{K}} \|y\|_I^2$.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/orthogonality_closure.tex`
- `papers/bedc/parts/concrete_instances/innerproduct/parallelogram_norm_seed.tex`
- `papers/bedc/parts/concrete_instances/innerproduct/norm_metric_seed.tex`
- `papers/bedc/parts/concrete_instances/innerproduct/core_surface.tex`

Rationale:
Halmos/Axler textbook chapter on inner-product spaces opens with three results: orthogonality symmetry, Pythagorean theorem, and parallelogram identity. The chapter has orthogonality symmetry (thm:innerproduct-orthogonality-symmetry-row at orthogonality_closure.tex:1), zero-side and additive-closure rows for orthogonality (thm:innerproduct-orthogonal-additivity-row at orthogonality_closure.tex:67), and the parallelogram identity (thm:innerproduct-parallelogram-identity-row at parallelogram_norm_seed.tex:30) — but Pythagorean is missing. Verified absent: grep across all parts/ finds 'Pythagorean' only in trig identity files (thm:real-analytic-pythagorean, thm:cplx-pythagorean), not in inner-product context. Inputs all present: linearity row thm:innerproduct-vecspace-linearity-row ✓ (used in parallelogram proof to expand $\langle x+y, x+y\rangle$), thm:innerproduct-orthogonality-symmetry-row gives $\langle x,y\rangle\sim_K 0_K \Rightarrow \langle y,x\rangle\sim_K 0_K$ ✓, thm:innerproduct-norm-squared-carrier-row interprets $\|\cdot\|^2$ as the diagonal $\langle\cdot,\cdot\rangle$ ✓, ring zero-addition laws ✓. Proof sketch is a 4-line specialization of the parallelogram proof: expand $\langle x+y,x+y\rangle$ by linearity into $\langle x,x\rangle + \langle x,y\rangle + \langle y,x\rangle + \langle y,y\rangle$, drop the two cross terms by orthogonality + symmetry, repack. 1-3 round closeable. Lands in parallelogram_norm_seed.tex (125 lines) as adjacent theorem.

---

### B-509 - EnumPerm composition associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | EnumPerm composition associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For finite BEDC-history spines $xs,ys,zs,ws$, if $\mathsf{EnumPerm}_{A,\sim_A}(xs,ys)$, $\mathsf{EnumPerm}_{A,\sim_A}(ys,zs)$, and $\mathsf{EnumPerm}_{A,\sim_A}(zs,ws)$ hold, then the two composite enumeration permutations from $xs$ to $ws$ obtained by left-association versus right-association coincide as $\mathsf{EnumPerm}$ witnesses (their forward and inverse position maps are identified).

Local inputs:
- `papers/bedc/parts/concrete_instances/90_finset_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/94_permutation_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/95_symgroup_namecert_construction.tex`

Rationale:
Hungerford ch.I.3 opens with the three group axioms applied to Sym(n): identity, inverse, associativity of permutation composition. The FinSet chapter has reflexivity (thm:enumperm-identity-reflexivity at 90_finset_namecert_construction.tex:528), symmetry (thm:enumperm-inverse-symmetry at 90_finset_namecert_construction.tex:487), and transitivity / composition closure (thm:enumperm-transitivity-by-bijection-composition at 90_finset_namecert_construction.tex:197), with the building-block lem:finset-enum-position-bijection-composition (90_finset_namecert_construction.tex:178). The fourth group axiom — composition associativity — is missing. Verified absent: grep for 'enumperm.assoc' / 'enumeration-permutation-association' returns nothing. SymGroup composition associativity is asserted in thm:symgroup-composition-inverse-action-obligations (95_symgroup_namecert_construction.tex:75) but routes through 'BHist graph reads + Pkg transport' rather than the underlying EnumPerm associativity, leaving the FinSet chapter's permutation algebra incomplete. Closes in 1-3 rounds: function composition over Pos(_) is associative by primitive Lean identity; the EnumPerm definition (forward + inverse + two inverse identities) carries through both bracketings to the same forward-and-inverse pair. Lands in 90_finset_namecert_construction.tex (621 lines, room).

---

### B-510 - AffineSpace action additivity (vector-translation cocycle)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AffineSpace action additivity (vector-translation cocycle) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If p is a carried point row in an AffineSpaceUp carrier and v,w are carried VecSpaceUp vector translation rows, then act(p, v +_V w) is classified by AffCls with act(act(p,v), w).

Local inputs:
- `papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex`

Rationale:
184_affinespace_namecert_construction.tex defines `act(p,v) := Cont(p, trans(v))` (line 22-25 of def:affinespace-history-torsor-carrier) and lists ten torsor obligations as theorems (action_closure, action_coverage, vector_difference, separation, vector_action_stability, free_action, transitive_action, classifier_transport, ledger_exactness, namecert_obligation_surface — all in lines 43-172). The cocycle/homomorphism identity `act(p, v+w) ~ act(act(p,v), w)` is conspicuously absent: grep '\label{thm:affinespace' returns 12 labels, none for action additivity, and grep 'cocycle\|action.*additive\|action.*compose' returns 0 inside the chapter. This is the missing torsor structural identity. Proof builds on Cont associativity (already cited at line 108, 155), the VecSpaceUp addition row supplied by NameCert_VecSpaceUp dependency (line 4), and the trans-as-group-hom field implicit in the lambda packing of the carrier (line 22-25). Not in BOARD title index — closest is B-409 graph three-step path reassociation, structurally different. Concrete single-implication form, lands cleanly in a 184-line file far from the 800-line cap.

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

### B-512 - FirstOrder deduction ledger concatenation closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FirstOrder deduction ledger concatenation closure |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If two accepted FirstOrderUp deduction ledgers D1 and D2 share an endpoint formula row, then their concatenation D1 ⧺ D2 is also an accepted FirstOrderUp deduction ledger over the same SetUp and TreeUp dependency certificates.

Local inputs:
- `papers/bedc/parts/concrete_instances/175_firstorder_namecert_construction.tex`

Rationale:
175_firstorder_namecert_construction.tex (115 lines) has only 3 theorems (grep '\\begin{theorem}' = 3): formula_carrier_obligation, deduction_soundness_ledger_obligation, namecert_obligation_surface. The ledger soundness theorem (line 62-87) inducts on the finite displayed deduction ledger and verifies acceptance for empty and step cases, but does NOT package the natural concatenation closure. grep for 'concat\|append.*ledger\|join.*deduction' in the file: 0 matches. This is the standard cut-rule shape for proof systems and is the prerequisite for any future soundness/completeness theorem that builds longer derivations from named lemmas. The proof induct-on-D2 / step-case reuses the existing acceptance condition at the join point; no new carrier datum needed. Not in BOARD title index — ranges over deduction concatenation, distinct from B-447 LP complementary slackness or the 'category' associativity entries. Concrete implication, fits cleanly in the 115-line file (well below cap).

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
