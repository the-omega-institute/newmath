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

### B-551 - Pullback ledger composition associativity at the gap-policy level

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Pullback ledger composition associativity at the gap-policy level |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If τ1:D'→D, τ2:D''→D', τ3:D'''→D'' each carry a classifier-preserving pullback ledger over Π and GapPol(Π,D) holds, then the composite pulled-back gap predicates obtained by ((τ1∘τ2)∘τ3) and (τ1∘(τ2∘τ3)) are logically equivalent on every D'''-source/token pair.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`

Rationale:
papers/bedc/parts/proof_obligations/gap_policy.tex defines the classifier-preserving pullback ledger at line 109 and proves the n-fold composite case `thm:composite-pullback-gap-policy-preserves-coverage-and-separation` at line 197 (B-504) plus the identity unit law `thm:identity-pullback-gap-policy-unit-law` at line 269 (B-550). Associativity of pullback composition is the missing third law that closes the categorical structure (identity + composition + associativity), and is not implied by either existing theorem since each one only fixes a single composition order. Grep `pullback.*associat|pulled-back.*associat|composite-pullback.*associat` across papers/bedc/parts/ returns zero matches. The file is 324 lines, well under the 760-line cap, with the existing pullback section ending at line 324 — clean append point. The proof is a chain unfolding of `def:classifier-preserving-pullback-ledger` clause (ii) twice on each side and reducing to the underlying composition equality τ1(τ2(τ3 h''')) = (τ1∘(τ2∘τ3))(h''') = ((τ1∘τ2)∘τ3)(h'''), then folding back.

---

### B-552 - ZNormal predicate is closed under HSame transport

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ZNormal predicate is closed under HSame transport |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If ZNormal(h) and HSame(h, k), then ZNormal(k).

Local inputs:
- `papers/bedc/parts/concrete_instances/257_zeckendorf_normal_namecert_construction.tex`

Rationale:
Sister chapter 254 (axisnat) explicitly proves the parallel HSame-transport lemma for ZeroSpine; the structurally analogous ZNormal predicate in 257 (Zeckendorf) is missing it. The chapter's classifier specification defines the classifier as HSame restricted to the carrier, which is logically distinct from the predicate itself being closed under HSame transport — closure is a structural induction over the ZNormal derivation, not a definitional unfolding. Fills a clear asymmetry gap a referee would flag, lands cleanly in a 203-line file, and proof is by induction on ZNormal(h) with HSame constructor inversion.

---


### B-553 - Zero-spine source shape exhaustion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Zero-spine source shape exhaustion |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
For every history h with ZeroSpine(h), either HSame(h, empty) or there exists h_pred with HSame(h, E0(h_pred)) and ZeroSpine(h_pred).

Local inputs:
- `papers/bedc/parts/concrete_instances/254_axisnat_namecert_construction.tex`

Rationale:
Chapter 254 has the empty base, closure under E0, E0-inversion, no-E1-extension, and HSame-transport for ZeroSpine, but no constructor-exhaustion theorem giving a binary case-disjunction over arbitrary ZeroSpine witnesses. Distinct from E0-inversion (which assumes the form E0(h_pred)) and from no-E1-extension (a negative result on a different constructor). Used downstream wherever ZeroSpine is consumed by case analysis without an explicit exhaustion citation. 144-line file is safe; theorem is one structural induction.

---


### B-554 - NetworkFlow zero feasible flow has minimum value among feasible flows

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | NetworkFlow zero feasible flow has minimum value among feasible flows |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
For any feasible NetworkFlowUp s-t flow F over capacity assignment u, FlowValue(F0) prefix-leq_NatUp FlowValue(F), where F0 is the zero edge-flow.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`

Rationale:
Chapter 211 has the max-extreme fully theoremed (residual-exhaustion optimality, equality-implies-optimality, weak duality) and the existence of the zero feasible flow at value zero (B-521), but the dual extremal statement — that the zero flow is the minimum-value feasible flow — is missing. Composite consequence using lem:networkflow-unary-fold-constant-empty and thm:preorder-prefix-empty-left-iff-unary, both already cited in the existing zero-feasibility proof. Distinct from B-521 (which only asserts feasibility at value 0, not extremality). 564-line file is under cap and the theorem lands in under 30 lines.

---

### B-555 - Ideal intersection greatest lower bound under inclusion preorder

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Ideal intersection greatest lower bound under inclusion preorder |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
For ideals I,J over a RingUp certificate with inclusion predicate ⪯_R, the intersection I∩_R J satisfies (I∩_R J) ⪯_R I, (I∩_R J) ⪯_R J, and any K ⪯_R I and K ⪯_R J jointly imply K ⪯_R (I∩_R J).

Local inputs:
- `papers/bedc/parts/concrete_instances/ideal/02_lattice_sum_surface.tex`

Rationale:
Hungerford / Atiyah-Macdonald characterize ideal lattice with both meets (intersection) as GLB and joins (sum) as LUB. The chapter has `thm:ideal-sum-least-upper-bound` (line 157) but no matching greatest-lower-bound theorem for intersection — only `thm:ideal-intersection-closure` (line 47). The proof unfolds intersection (Definition line 39) and inclusion (Definition line 93) directly: (I∩J)(x) ⇒ I(x) ∧ J(x), so projection laws are immediate; for the universal property, K(x) ⇒ I(x) and K(x) ⇒ J(x) jointly give K(x) ⇒ I(x) ∧ J(x). 1 round closure. Lands in 02_lattice_sum_surface.tex (270 lines).

---

