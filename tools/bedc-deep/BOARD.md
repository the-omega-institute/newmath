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

### B-558 - Max-flow value lifts to a primal LP optimum bridge between NetworkFlow and LPDuality

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Max-flow value lifts to a primal LP optimum bridge between NetworkFlow and LPDuality |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For a NetworkFlowUp carrier G with capacity u, feasible flow F, and residual-cut exhaustion certificate Xi, the flow-value endpoint V_F and cut-capacity endpoint K_Xi assemble a primal-dual LPDualityUp feasible pair over the carrier's unary scalar field whose strong-duality classifier returns the same hsame endpoint.

Local inputs:
- `papers/bedc/parts/concrete_instances/211_networkflow_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/213_lpduality_namecert_construction.tex`

Rationale:
This is a genuine bridge target between two existing concrete_instances chapters that the project_governance roadmap pairs but never wires up: 211_networkflow already proves V_F hsame K_Xi via residual-cut exhaustion (B-463, B-554) and 213_lpduality already provides strong-duality classifier data over abstract ordered fields (B-516/B-519/B-525/B-540/B-549). What is missing is the assembly map: certificate-grade max-flow data → primal-dual LP feasible pair with classifier coincidence. None of the existing BOARD entries do this; B-554 is single-side optimality only, the LPDuality entries are face/feasibility transports on the LP side alone, and B-447/B-444/B-429 stay inside the LP carrier. The candidate also flags the right landing-safety move: 211_networkflow is near cap, so this lands in a new sibling 211_networkflow_lpduality_bridge.tex rather than mutating either existing file. Concrete implication form, in BEDC scope, no paper duplicate.

---

### B-562 - Polynomial evaluation at the multiplicative unit equals additive fold of coefficients

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial evaluation at the multiplicative unit equals additive fold of coefficients |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under a scalar $\RingUp$ certificate $R$ with multiplicative unit $1_R$, for every carried coefficient spine $p$, $\mathsf{Eval}_{1_R,R}(p) \sim_R \mathsf{fold}_{+,R}(\mathsf{trim}_R(p))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_eval.tex`
- `papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex`

Rationale:
Belongs to the Polynomial chapter (25_polynomial). Textbook standard: Hungerford *Algebra*, ch.III §5 (polynomial evaluation), and any introductory abstract algebra textbook treats the identity $p(1) = a_0 + a_1 + \dots + a_n$ as the most basic specialisation of polynomial evaluation. The chapter has 'evaluation at zero returns the constant coefficient' as a stated theorem (file 25_polynomial_literal_addtrim_eval.tex line 442), evaluation is additive (line 113), evaluation is multiplicative (line 330), but the symmetric specialisation 'evaluation at one returns the sum of coefficients' is not stated. Closes in 1-3 codex rounds: the recursive Horner clause at $\alpha = 1_R$ collapses the multiplicand $\alpha\cdot u$ to $u$ via the scalar multiplicative left-unit row of $\RingUp$ (already cited multiple times in 26_fps_ringup_tail.tex line 68), and structural induction on the trimmed coefficient spine identifies the iterated Horner result with the finite additive fold (the lemma $\autoref{thm:finite-additive-fold-congruence-coefficient-lists}$ of file 25_polynomial_namecert_construction.tex line 525 is exactly the fold-side congruence prerequisite). All references already exist in the polynomial chapter.

---

### B-563 - ProbSpace ternary inclusion-exclusion identity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ProbSpace ternary inclusion-exclusion identity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 8/10 |

Problem:
Given a ProbSpace^↑ carrier P with measurable events A,B,C and binary cover-difference ledgers for each pair, mu(A ∪ B ∪ C) + mu(A ∩ B) + mu(A ∩ C) + mu(B ∩ C) ~_R mu(A) + mu(B) + mu(C) + mu(A ∩ B ∩ C).

Local inputs:
- `papers/bedc/parts/concrete_instances/162_probspace_namecert_construction.tex`

Rationale:
162_probspace_namecert_construction.tex:213 establishes the binary inclusion-exclusion identity (thm:probspace-binary-inclusion-exclusion-identity, B-503 on BOARD) using def:probspace-binary-cover-difference-ledger (line 189). Grep for `ternary.*inclusion|three.*inclusion|triple.*inclusion|ProbSpace.*[Tt]ernary` returned no matches in papers/ or lean4/. The natural ternary version is the next layer in the same chapter; the proof composes the binary identity twice (at A vs (B ∪ C) and then at B vs C), using the binary cover-difference ledger plus the AbGroupUp additive congruence rows already invoked at line 249. File at 281 lines, ample room. Distinct from B-530 'Measure ternary-union subadditivity' (Measure-side subadditivity, not inclusion-exclusion equality on ProbSpace).

---
