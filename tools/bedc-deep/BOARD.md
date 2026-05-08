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

### B-503 - ProbSpace binary inclusion-exclusion identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ProbSpace binary inclusion-exclusion identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If A,B are measurable events in a ProbSpace, then \mu(A\cup B)+\mu(A\cap B)\sim_R\mu(A)+\mu(B).

Local inputs:
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`

Rationale:
Genuinely missing companion in 162_probspace_namecert_construction.tex. BOARD has B-358 (complement-mass additivity), B-400 (complement = 1 − event-mass), B-435 (monotone bounds), and B-433 (measure binary-union subadditivity), but none packages the equality form for non-disjoint two-event pairs. The relative-difference row + finite-disjoint-union additivity decompose A∪B and B into disjoint pairs that add up to μ(A)+μ(B), giving the identity directly. This is the prerequisite shape downstream Distribution↑/Independence↑/CondExp↑ joint-event reasoning will repeatedly want, and the file (~178 lines) lands it cleanly without needing a split. Concrete implication form, in scope, not a parameter echo.

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
