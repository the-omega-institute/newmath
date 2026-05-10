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

### B-622 - MarkovChain transition packet finite-prefix restriction is a MarkovChain carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MarkovChain transition packet finite-prefix restriction is a MarkovChain carrier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
If a finite MarkovChain BHist transition packet over a unary time ledger of length n+k is accepted by the MarkovChainUp carrier, then its restriction to the first n displayed time rows (with the first n+1 RandomVarUp rows, n DistributionUp law rows, n transition rows, and inherited Cont/Pkg provenance) is again an accepted MarkovChainUp carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/167_markovchain_namecert_construction.tex`

Rationale:
The MarkovChain carrier is inductive on a unary time ledger but the chapter exposes only kernel-classifier stability, transition-ledger exactness, source boundary, and obligation-surface theorems — no prefix-truncation closure. Future Martingale/Brownian-compatibility and hitting-time consumers need it. Distinct from B-511 Independence finite subfamily projection (different carrier: independence index family vs time ledger). Lands cleanly in the existing 167_markovchain file with a unary-ledger induction; the proof is structural, not deep.

---

### B-623 - MarkovChain transition packet end-to-end concatenation closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MarkovChain transition packet end-to-end concatenation closure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If P1 is an accepted MarkovChainUp transition packet over time ledger of length n with terminal RandomVarUp row X_n and P2 is an accepted MarkovChainUp transition packet over time ledger of length m starting from a RandomVarUp row Y_0 with X_n hsame Y_0 over a shared ProbSpaceUp source, then their displayed concatenation along that shared endpoint is an accepted MarkovChainUp transition packet over a unary time ledger of length n+m.

Local inputs:
- `papers/bedc/parts/concrete_instances/167_markovchain_namecert_construction.tex`

Rationale:
Strict companion to the prefix-restriction proposal but technically distinct (gluing along shared endpoint vs prefix truncation). Together they make MarkovChainUp carriers a true list-with-restriction-and-concatenation closure. The Newton concatenation candidate has the same proof skeleton in a different chapter, so this is a parallel, not duplicate, work item. No paper coverage of the gluing law and no BOARD dedup; the kernel-classifier-stability theorem alone is insufficient for downstream sub-chain construction. Codex_close-shaped: splice ledgers, reapply kernel classifier stability at the splice index.

---

### B-624 - Matrix transpose of the zero matrix is the zero matrix with swapped dimensions

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Matrix transpose of the zero matrix is the zero matrix with swapped dimensions |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Over a scalar RingUp carrier with classifier sim_R and zero endpoint 0_R, the transpose of the carried zero matrix Z_{n,m} is classified pointwise as the zero matrix Z_{m,n} via def:matrix-transpose-certified-scalar-carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_transpose.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_zero_matrix_absorption.tex`

Rationale:
The matrix chapter has both transpose and zero-matrix data plus extensive transpose laws (transpose-reverses-product, double-readback involution, preserves-addition) but no transpose/zero interaction lemma. This is the most basic missing companion law and its absence is the kind of referee-flagged gap that propagates into Banach/Hilbert operator chapters. Pointwise unfold + classifier substitution; clean codex_close. Distinct from the identity-matrix transpose candidate which has a different proof shape (Kronecker delta symmetry).

---

### B-625 - Matrix transpose of the identity matrix is the identity matrix

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Matrix transpose of the identity matrix is the identity matrix |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
Over a scalar RingUp carrier with classifier sim_R, multiplicative unit 1_R, and zero endpoint 0_R, the transpose of the finite-fold identity matrix I_n is classified pointwise as the same identity matrix I_n via def:matrix-transpose-certified-scalar-carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_transpose.tex`
- `papers/bedc/parts/concrete_instances/matrix/finite_fold_multiplication_laws_fold_identity.tex`

Rationale:
Genuinely distinct from the transpose-zero candidate: the proof relies on Kronecker-delta symmetry at (i,j) vs (j,i), not zero pointwise. Together with transpose-zero this completes the elementary transpose/distinguished-matrix lemmas that downstream Hermitian/orthogonal/unitary consumers expect. No BOARD entry; not in the paper's existing transpose theorem list. Clean codex_close on entrywise readback.

---

### B-626 - InnerProduct two-vector Gram diagonal scalar-nonnegativity row exposure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | InnerProduct two-vector Gram diagonal scalar-nonnegativity row exposure |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For the InnerProductUp two-vector Gram source of def:innerproduct-two-vector-gram-source with carried vectors x,y, the diagonal scalar endpoints langle x,x rangle and langle y,y rangle satisfy 0_scal le_scal langle x,x rangle and 0_scal le_scal langle y,y rangle under the inherited scalar order, derived from the Gram source's retained diagonal positivity rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/two_vector_gram_boundary.tex`

Rationale:
The Gram source explicitly retains diagonal positivity rows and the consumer boundary cites them, but no theorem reads them back as a public scalar-order inequality. Hilbert / Riemannian / RootSystem certificates need this exposed. Distinct from B-528 ternary Pythagoras, B-573 norm-sq scalar factoring, and B-507/B-514 polarization-difference identities — none of those expose diagonal nonnegativity through the scalar order namecert. Oracle_likely flag from candidate is appropriate; bridge between InnerProductUp positivity predicate and scalar-order namecert may need small interface work but the claim itself is concrete.

---

### B-627 - Brownian path-step carrier finite-prefix restriction is a BrownianUp carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Brownian path-step carrier finite-prefix restriction is a BrownianUp carrier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If an accepted BrownianUp BHist process packet of def:brownian-bhist-process-packet over a unary time ledger of length n+k is given, then restricting the displayed time-step rows, increment ledger entries, continuity rows, and Cont/Pkg provenance to the first n time steps yields a finite BHist process packet that is again accepted by the BrownianUp carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/169_brownian_namecert_construction.tex`

Rationale:
Carrier-level prefix closure for Brownian. Genuinely distinct from the MarkovChain prefix candidate: Brownian carries a continuity row and Gaussian-increment ledger that the MarkovChain transition row does not, so the projection step is non-trivially different (continuity-ledger truncation must preserve modulus-of-continuity witnesses). Future Martingale-Brownian compatibility consumers (cf. paper line 416) demand it. No BOARD or paper coverage. Codex_close on unary-ledger induction with continuity-row reprojection.

---
