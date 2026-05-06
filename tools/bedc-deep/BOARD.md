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

### B-475 - Distribution pushforward sigma-additivity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Distribution pushforward sigma-additivity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If a DistributionUp pushforward is induced by a RandomVarUp map whose preimages preserve countable target unions and the source MeasureUp surface is sigma-additive, then the pushed-forward target measure classifies a countable disjoint union by the countable sum of the pushed-forward component measures.

Local inputs:
- `papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface.tex`
- `papers/bedc/parts/concrete_instances/measure/carrier_surface_rows.tex`

Rationale:
Distribution currently has pushforward total mass at papers/bedc/parts/concrete_instances/164_distribution_namecert_construction.tex:12, finite binary disjoint-union additivity at :93, monotonicity at :203 and :330, and relative-difference additivity at :250. The finite additivity proof explicitly consumes the binary RandomVar preimage theorem at 164_distribution_namecert_construction.tex:105, while the MeasureUp surface already provides countable-disjoint sigma-additivity at papers/bedc/parts/concrete_instances/measure/carrier_surface.tex:205-223 and countable-sum classifier stability at :237-246. Focused grep for `distribution.*countable|pushforward.*sigma` under parts returned 0 theorem labels; hits were roadmap prose and existing finite/binary distribution material. The distribution file is 375 lines, so it is a viable body-file target.

---

### B-478 - CondExp projection idempotence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CondExp projection idempotence |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
If CondExpUp(X,G) is the conditional expectation of an integrable RandomVarUp endpoint onto a sub-sigma-algebra G, then applying the same CondExpUp projection again is classifier-equal to the first conditional expectation under the HilbertUp L2 projection surface.

Local inputs:
- `papers/bedc/parts/concrete_instances/166_condexp_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/163_randomvar_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/69_hilbert_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/hilbert_orthogonal_projection_row.tex`

Rationale:
CondExpUp is described as the L2 projection of an integrable random variable onto the subspace measurable with respect to a sub-sigma-algebra at papers/bedc/parts/concrete_instances/166_condexp_namecert_construction.tex:4. That chapter has 10 lines, 0 theorem environments, and 0 Lean markers in the inventory. A related singleton Hilbert projection idempotence theorem exists at papers/bedc/parts/concrete_instances/hilbert_orthogonal_projection_row.tex:60-73, but focused grep for `condexp|conditional[- ]expect|tower law|tower property|conditional expectation.*idempot|condexp.*idempot` returned no CondExp theorem labels; hits were roadmap prose, dependency mentions in Bayesian/Martingale chapters, and the CondExp chapter header. The proposed result is the concrete idempotence law for the conditional-expectation object itself.

---

### B-481 - Banach bounded-operator identity units

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Banach bounded-operator identity units |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If BanachBLOp(C,D,T,K,Lambda) holds and the identity maps on C and D carry the unit bound, then T composed with id_C and id_D composed with T are carried and classify with T.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex`

Rationale:
This is a concrete two-sided unit law for an existing Banach operator composition surface. Existing coverage includes carrier and composition structure but not the identity-unit theorem, and the target is not duplicated by any current BOARD entry.

---

### B-485 - Simplicial union carrier face closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Simplicial union carrier face closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If finite simplicial carriers K and L share the simplex-code source, classifier, and face relation, and js enumerates the pointwise union predicate Simplex_K or Simplex_L, then the union predicate is face-closed and inherits face transitivity.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a concrete closure counterpart to the existing simplicial intersection carrier results. It belongs cleanly in the simplicial-complex chapter, has a direct implication shape, and does not duplicate any current BOARD target or listed paper theorem.

---

### B-486 - Unitary conjugation channel composition law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Unitary conjugation channel composition law |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the QuantumChannelUp and UnitaryGroupUp setup on a Hilbert carrier H, carried unitary automorphisms U and V imply that Ad_U composed with Ad_V is the QuantumChannel endpoint classified by Ad_{U\circ V}.

Local inputs:
- `papers/bedc/parts/concrete_instances/199_quantumchannel_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/197_unitarygroup_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/191_operatorideal_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/69_hilbert_namecert_construction.tex`

Rationale:
The candidate is a concrete implication landing directly in the existing quantum-channel surface. It is distinct from the paper's current QuantumChannel composition closure and Unitary conjugation is a QuantumChannel theorem: those establish channel closure and single-unitary conjugation, but do not state the endpoint-identification law for the composite conjugation channel against the product unitary. It is not marker-only, not a BOARD duplicate, and the main landing file is below the line cap.

---
