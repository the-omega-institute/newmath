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

### B-518 - AbelianCat zero morphism left-absorbing under composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AbelianCat zero morphism left-absorbing under composition |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For carried hom $f \in \mathcal{H}(X,A)$ in an $\AbelianCatUp$ additive kernel-cokernel carrier, the displayed composite $0_{A,B}\circ f$ is classified by $\sim_{X,B}$ with the displayed zero morphism $0_{X,B}$.

Local inputs:
- `papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex`

Rationale:
AbelianCat is a 433-line chapter with 10 theorems but only B-423 (`AbelianCat hom zero morphism uniqueness`, line 380) and B-437 (kernel/cokernel factor uniqueness) completed. The zero-morphism API in 154_abeliancat_namecert_construction.tex:380-421 establishes that $0_{A,B}$ is the unique left/right additive identity but never asserts the corresponding composition-annihilation row that makes zero morphisms `compose to zero'. This is the foundational fact that turns the existing zero-biproduct surface (\autoref{thm:abeliancat-additive-zero-biproduct-obligation} at line 79) into a usable abelian-category obligation. Single implication, concrete, in chapter scope. No abstract carrier transport — this is content over the displayed hom carriers. No collision with BOARD index B-407..B-516 or completed list.

---

### B-538 - Quadrature empty-node sum is zero

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Quadrature empty-node sum is zero |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For a finite weighted QuadratureUp rule Q=(xs,alpha,omega,I_Q), if the FinSetUp node spine xs is empty, then for every finite polynomial-code spine p the quadrature fold QSum_Q(p) is scalar-classifier-equal to 0_R.

Local inputs:
- `papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex`

Rationale:
QuadratureUp has completed coverage for the exactness-degree classifier, but that coverage is concentrated on degree weakening, reflexivity, transitivity, and preorder rows: see the definitions of QSum_Q and DegBoundLe at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:21-66 and the completed theorem suite at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:105-240. The concrete rule-level fold itself is defined as a finite additive fold over Pos(xs) at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:27-31, while the existing ledger theorem only states that this is the carried exactness surface at papers/bedc/parts/concrete_instances/205_quadrature_namecert_construction.tex:90-103. The empty-node boundary is not one of B-428, B-451, or B-465 and is a small concrete implication about the actual quadrature sum rather than another degree-classifier law.

---
