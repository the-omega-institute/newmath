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

### B-559 - RealAnalytic CosPart at empty input is identically the constant-one stream

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RealAnalytic CosPart at empty input is identically the constant-one stream |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
If a $\RealUp$ history $x$ is classified to $\emp$ and supplied limit witness $\mathsf{Cos}(x,c)$ together with limit-uniqueness rows comparing $\mathsf{CosPart}(x,\cdot,\cdot)$ with the constant-one rational stream are present, then $\mathsf{RealClassifier}(c, \Eone(\emp))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/52_real_analytic_namecert_construction.tex`

Rationale:
Belongs to the Real Analytic chapter. Textbook standard: Apostol, *Mathematical Analysis*, §8.21 (cosine series) treats $\cos 0=1$ as the very first trigonometric value; Rudin *Principles of Mathematical Analysis*, §8.7 likewise. Currently the chapter only states the addition formula (line 535-558), the Pythagorean identity (line 387-395), and sin-pi-multiples (line 397-405) — and the latter explicitly assumes 'supplied limit-uniqueness classifier rows for the base values $\sin(0)$ and $\sin(\mathsf{Pi})$' (line 399), confirming neither base value is internally established. Closes in 1-3 codex rounds: at $x=\emp$, the recursive definition of $\mathsf{CosPart}$ (line 369-371) gives $C_0 = 1$, and every successor term contains the factor $x^{2k} = 0$ for $k\ge 1$ (zero-power vanishing under $\RealAlgOrder$ multiplication rows already cited in line 326). Infrastructure already present: $\RealAlgOrder$ rows for products and powers, unary factorial denominators, supplied $\RealUp$ limit and uniqueness rows. The lemma uses the same shape as the existing exp-additivity (line 324) and Pythagorean (line 387) theorems.

---


### B-560 - RealAnalytic SinPart at empty input is identically the zero stream

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RealAnalytic SinPart at empty input is identically the zero stream |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 10/10 |
| Novelty | 6/10 |

Problem:
If a $\RealUp$ history $x$ is classified to $\emp$ and supplied limit witness $\mathsf{Sin}(x,s)$ together with limit-uniqueness rows comparing $\mathsf{SinPart}(x,\cdot,\cdot)$ with the constant-zero rational stream are present, then $\mathsf{RealClassifier}(s, \emp)$.

Local inputs:
- `papers/bedc/parts/concrete_instances/52_real_analytic_namecert_construction.tex`

Rationale:
Belongs to the Real Analytic chapter. Textbook standard: Apostol §8.21, Rudin §8.7 — $\sin 0 = 0$ is the canonical base case for sine identities. This is currently a *supplied hypothesis* of $\autoref{thm:real-analytic-sin-pi-multiples}$ (file 52_real_analytic_namecert_construction.tex line 399 and 402: 'The trigonometric witnesses and classifier rows supply the base values $\sin(0)$ and $\sin(\mathsf{Pi})$ as zero'). Internalising sin(0)=0 as a kernel theorem turns one of the two supplied base rows into an established lemma, tightening sin-pi-multiples without touching the Pi machinery. Closes in 1-3 codex rounds: at $x=\emp$, the recursive definition $\sum_{k=0}^n (-1)^k x^{2k+1}/(2k+1)!$ (line 371) has every term containing the factor $x^{2k+1} = 0$ (every odd power of zero vanishes under the $\RealAlgOrder$ multiplication rows). Infrastructure: same as cos(0)=1 candidate. No new prerequisites.

---


### B-561 - RealAnalytic ExpPart at empty input is identically the constant-one stream

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RealAnalytic ExpPart at empty input is identically the constant-one stream |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
If a $\RealUp$ history $x$ is classified to $\emp$ and supplied limit witness $\mathsf{Exp}(x,e)$ together with limit-uniqueness rows comparing $\mathsf{ExpPart}(x,\cdot,\cdot)$ with the constant-one rational stream are present, then $\mathsf{RealClassifier}(e, \Eone(\emp))$.

Local inputs:
- `papers/bedc/parts/concrete_instances/52_real_analytic_namecert_construction.tex`

Rationale:
Belongs to the Real Analytic chapter. Textbook standard: Apostol §8.20 (exponential series) and Rudin §8.6 take $\exp 0 = 1$ as the foundational identification preceding every multiplicative property. Currently the chapter has no theorem stating exp(0)=1; the additivity theorem (line 324-333) treats the additive identity case implicitly by way of supplied limit witnesses for both arguments. Closes in 1-3 codex rounds: at $x=\emp$, $\mathsf{ExpPart}(x,n,S_n) = \sum_{k=0}^n x^k/k!$ (line 111) collapses to $1 + 0 + 0 + \dots = 1$ since $x^k = \emp$ for $k \ge 1$ (zero-power vanishing) and $x^0/0! = 1_R$ by the unary factorial-denominator inverse already established in the chapter. Infrastructure already present: ExpPart definition (line 111), $\RealAlgOrder$ rows for products and powers (line 326), unary factorial-denominator inverses, supplied limit witness.

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

