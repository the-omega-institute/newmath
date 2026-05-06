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

### B-487 - Simplicial union face dimension grading

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Simplicial union face dimension grading |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If K and L share a face relation and a common grading row, then every face chain in Simplex_{K\cup L} inherits the carried dimension comparisons by case analysis on the upper simplex branch.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a concrete closure-style simplicial-complex theorem that lands in the same surface as B-485 without duplicating it: B-485 covers face closure and face transitivity for the union carrier, while this target adds the inherited grading/face-dimension monotonicity row. The claim is a single implication under shared carrier, face, and grading setup, and it is not marker-only or verification-axis work.

---


### B-488 - Simplicial union append enumeration

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | Simplicial union append enumeration |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If ks enumerates Simplex_K and ls enumerates Simplex_L under the shared simplex-code source and classifier, then ks++ls enumerates Simplex_{K\cup L}.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a concrete enumeration lemma for the simplicial union carrier and is a useful sibling/prerequisite to B-485 rather than a duplicate of its face-closure theorem. It has a precise implication shape, stays within the concrete_instances chapter, and supplies a natural construction of the union enumeration object assumed by the existing BOARD target.

---

### B-489 - Hash collision-freeness excludes second preimages

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Hash collision-freeness excludes second preimages |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
In the HashUp setup, CollFreeH and HashSecondPreimageSuccessH(x,y) imply contradiction by converting second-preimage success into HashCollisionSuccessH(x,y).

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`

Rationale:
This is a concrete security-facing obstruction theorem over the existing HashUp transcript surface. It is not a BOARD duplicate and not already packaged in the paper labels: existing rows convert second-preimage success to collision success, while this target names the collision-free budget and closes the impossibility consequence as a reusable theorem.

---


### B-490 - PublicKey certified ciphertext plaintext uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | PublicKey certified ciphertext plaintext uniqueness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
In the PublicKeyUp setup, PKDecryptEncryptExactP and PKDecryptOutputDetP together with PKKeyGenP(pk,sk), PKCertifiedEncP(pk,m,c), and PKCertifiedEncP(pk,n,c) imply muP(m,n).

Local inputs:
- `papers/bedc/parts/concrete_instances/221_publickey_namecert_construction.tex`

Rationale:
This is a concrete inversion theorem for certified ciphertext rows, distinct from the existing decrypt-encrypt and arbitrary-decryption statements. It packages the consequence that one generated keypair and one certified ciphertext cannot certify two classifier-distinct plaintexts, using existing exactness and output determinacy rows.

---


### B-491 - Banach bounded-operator bound weakening

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Banach bounded-operator bound weakening |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If BanachBLOp(C,D,T,K,Lambda), K <= Kprime, and Kprime is a carried nonnegative RealUp bound endpoint, then T is carried as BanachBLOp(C,D,T,Kprime,LambdaPrime) with the same structural rows and a weakened bound ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`

Rationale:
This fills a useful budget-monotonicity gap in the Banach bounded-linear-operator surface. It is not just classifier transport: it constructs a reusable weakened operator-bound carrier row from RealUp order transitivity, norm nonnegativity, and multiplication monotonicity.

---


### B-492 - Simplicial union inherits dimension grading

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Simplicial union inherits dimension grading |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If finite simplicial carriers K and L share the simplex-code source, face relation, and dimension map d, and the union predicate is finite and face-closed, then carried union faces and two-step face chains satisfy the inherited dimension inequalities.

Local inputs:
- `papers/bedc/parts/concrete_instances/216_simplicialcomplex_namecert_construction.tex`

Rationale:
This is a distinct union-side counterpart to the existing intersection dimension-grading theorem and to the active union face-closure target. It lands on a concrete finite simplicial carrier statement and gives a reusable grading row once the union carrier rows are in place.

---


### B-493 - Network-flow residual cut capacity determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Network-flow residual cut capacity determinacy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For a fixed feasible finite NetworkFlowUp s-t flow F, any two residual-cut augmenting-path exhaustion certificates Xi and Eta for F induce NatUp-classifier-equal residual cut capacities.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`

Rationale:
This is a compact determinacy theorem over the existing NetworkFlowUp residual-exhaustion surface. Existing paper content proves each residual exhaustion cut capacity equals FlowValue(F); this target packages the certificate-independence consequence, which is distinct from optimality.

---

