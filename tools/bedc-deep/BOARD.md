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

### B-610 - InnerProduct orthogonality left scalar-action closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | InnerProduct orthogonality left scalar-action closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For carried vectors x,y:C_V and a carried scalar r, if x \perp_I y then (r \cdot_V x) \perp_I y.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/orthogonality_closure.tex`

Rationale:
Direct missing companion to thm:innerproduct-orthogonality-right-scalar-action-closure (orthogonality_closure.tex:139). Symmetric left-slot version is not stated. Proof routes through orthogonality symmetry plus the existing right-scalar closure. Concrete BEDC closure target, lands in a 230-line file well under cap. Not paraphrase of any existing BOARD entry (B-573 is about norm-squared scalar factoring, distinct).

---


### B-611 - InnerProduct orthogonality left additive closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | InnerProduct orthogonality left additive closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For carried vectors x,y,z:C_V, if x \perp_I z and y \perp_I z then (x +_V y) \perp_I z.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/orthogonality_closure.tex`

Rationale:
Mirrored companion to thm:innerproduct-orthogonal-additivity-row (right-additive). Left-additive form is independently used by sublattice-of-orthogonals arguments; not currently stated. Proof: symmetry -> right-additivity -> symmetry. Distinct from the left-scalar and left-inverse candidates (different slot symmetry). Lands cleanly.

---


### B-612 - SpinGroup conjugation action identity law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | SpinGroup conjugation action identity law |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For SpinGroupUp packet S with Clifford-unit endpoint = identity e, every Clifford-vector row v satisfies Act_e(v) ~_CliffordUp v.

Local inputs:
- `papers/bedc/parts/concrete_instances/spingroup/boundary_consumer_exactness.tex`

Rationale:
Complements B-600 (conjugation multiplicativity). Together with the multiplicative law it makes the conjugation row a group action; the unit law is currently the missing half. Proof is a one-shot Clifford left/right unit collapse. Distinct from all existing SpinGroup BOARD entries.

---


### B-613 - Sheaf identity-refinement pullback identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Sheaf identity-refinement pullback identity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Pulling back a compatible family along the identity refinement returns the original family up to local section equivalence: rho_{iota(a),iota(a)}(s_a) ~_{iota(a)} s_a for every a.

Local inputs:
- `papers/bedc/parts/concrete_instances/sheaf/04_refinement_exactness.tex`

Rationale:
Distinct from B-520 (which only states that identity refinement is a refinement). This new target says the pullback functor evaluated at the identity refinement is the identity on compatible families. One-step proof from def:sheaf-indexed-section-presheaf-carrier identity-restriction field; underpins downstream gluing-uniqueness arguments that currently inline this step.

---


### B-614 - Measure head-tail iterated finite-prefix readback

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Measure head-tail iterated finite-prefix readback |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For a MeasureUp surface, measurable sequence E_*, and unary history n, Sigma_mu(E_*) ~_R mu(E_0) +_R ... +_R mu(E_{n-1}) +_R Sigma_mu(E_{*+n}).

Local inputs:
- `papers/bedc/parts/concrete_instances/measure/head_tail_tail_scope.tex`

Rationale:
Strict generalisation of thm:measure-head-tail-tail-countable-sum-scope (single step). N-step iterated form is the version downstream finite-additivity / countable-additivity prefix arguments actually consume. Finite induction on unary index using the existing single-step readback plus R-classifier transitivity. Distinct from B-598/B-530 (binary/ternary union subadditivity) and B-538 (empty-node sum).

---


### B-615 - InnerProduct orthogonality left additive-inverse closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | InnerProduct orthogonality left additive-inverse closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For carried vectors x,y:C_V, if x \perp_I y then (-_V x) \perp_I y.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/orthogonality_closure.tex`

Rationale:
Companion to thm:innerproduct-orthogonal-additive-inverse-closure (right slot). Left-slot symmetric version not stated; consumed together with right slot by signed-sum and sublattice-of-orthogonals constructions. Independent from the left-scalar and left-additive candidates: different slot symmetry (additive inverse). All three live in the 230-line orthogonality_closure.tex.

---

