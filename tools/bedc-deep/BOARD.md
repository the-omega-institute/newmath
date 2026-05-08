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


### B-504 - Composite gap policy n-fold pullback preserves coverage and separation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Composite gap policy n-fold pullback preserves coverage and separation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If \GapPol(\Pi,D) and \tau_1:D_1\to D, \tau_2:D_2\to D_1, \ldots, \tau_k:D_k\to D_{k-1} each carry a classifier-preserving pullback ledger over \Pi, then the k-fold composite \tau_1\circ\cdots\circ\tau_k carries a classifier-preserving pullback ledger satisfying coverage and separation over D_k.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`

Rationale:
Strict generalization, not a paraphrase. gap_policy.tex packages the single-step (line 152) and binary composite (line 196) cases, but the n-fold version is the form invoked downstream by proof_standing/04 and core/07's 'finite chain of compressions' arguments. Direct induction on chain length using the binary theorem closes it; lands in a 266-line chapter with no cap risk. No BOARD entry covers iterated pullback of gap policies, and the proof discharges as a clean inductive packaging — exactly the 'why only the binary case?' senior-referee gap that earns its own slot.

---


### B-505 - Sheaf refinement composition is classifier-associative on three-step towers

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Sheaf refinement composition is classifier-associative on three-step towers |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For displayed refinements (r,\epsilon):\mathcal V\to\mathcal U, (s,\eta):\mathcal W\to\mathcal V, (t,\zeta):\mathcal X\to\mathcal W of indexed sheaf covers, the composites ((r\circ s)\circ t) and (r\circ(s\circ t)) yield classifier-equal pulled-back compatible families on each indexed open of \mathcal X.

Local inputs:
- `papers/bedc/parts/concrete_instances/sheaf/05_refinement_composition_and_presentation.tex`

Rationale:
Composite consequence of two binary theorems already proved in sheaf/05_refinement_composition_and_presentation.tex (binary refinement composition + binary refinement-pullback composition). Three-step composition is invoked downstream by sheaf/08_triple_overlap_route_ledger.tex and sheaf/06_restricted_common_refinement_exactness.tex but never packaged as a named theorem. Closure proof is a routine two-application argument plus carrier-section classifier transitivity. Lands as a sibling theorem in a 198-line file — well below cap. No BOARD entry on sheaf refinement associativity, no overlap with B-352 (sheaf gluing uniqueness) or B-365 (global restriction local-family compatibility).

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

