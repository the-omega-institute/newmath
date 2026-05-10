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

### B-638 - HopfAlgUp antipode fixes the unit row of the bialgebra

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | HopfAlgUp antipode fixes the unit row of the bialgebra |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For an accepted HopfAlgUp bialgebra packet of \autoref{def:hopfalg-bhist-bialgebra-carrier} with displayed antipode row S, the antipode of the unit endpoint η(1) classifies (\sim_{HopfAlgUp}) with η(1) itself, read through the convolution-inverse obligation rows of \autoref{thm:hopfalg-antipode-convolution-inverse-obligation}.

Local inputs:
- `papers/bedc/parts/concrete_instances/158_hopfalg_namecert_construction.tex`

Rationale:
File 158_hopfalg_namecert_construction.tex (336 lines) has 13 theorems but the canonical Hopf-algebra fact `S(1) = 1` is missing. grep for `S(1)|antipode unit|antipode of the unit|antipode applied to` finds only mentions of unit-counit endpoints in convolution context, never the elementary endpoint identity. The completed BOARD has B-529 HopfAlgUp antipode uniqueness from convolution-inverse witnesses but not antipode-on-unit, which is a strictly weaker, single-implication consequence of the convolution-inverse rows already exported in lines 63–82. Within scope, single implication, no host equality.

---

### B-640 - MatroidUp restriction to empty subset has only the empty independent family

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | MatroidUp restriction to empty subset has only the empty independent family |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
For a MatroidUp independent-set certificate over ground predicate E with naming certificate cert and a restriction subset K of \autoref{def:certified-matroid-restriction-rows} taken as the empty predicate λz.⊥, the restricted independent family Ind_{M|K} accepts only the empty independent set λz.⊥, exposed by the same finite-spine ledger that records empty_M.

Local inputs:
- `papers/bedc/parts/concrete_instances/180_matroid_namecert_construction.tex`

Rationale:
180_matroid_namecert_construction.tex (381 lines) has only 3 theorems: intersection-preserves-independence, restriction certificate, and restrictions compose. The boundary case `restrict to ∅` — a degenerate, single-implication concrete instance — is missing. grep for `empty subset|emptyset|restriction.*to.*empty` shows only the global `empty_M` axiom row, never an empty-restriction theorem. Restriction is one of the few combinatorial operations BEDC has registered for matroids, but only the structure-preservation and composition theorems exist, not boundary-input concrete instances. File at 381/800.

---

### B-641 - FftUp length-one schedule classifies with the input row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FftUp length-one schedule classifies with the input row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For a FftUp packet of \autoref{def:fft-namecert-construction} whose carrier butterfly schedule has length-one (singleton index family from the dependent NameCert_{FourierUp}/NameCert_{ComplexUp}), the FFT output row classifies (\sim_{ComplexUp}) with the input row, read through the butterfly obligation and ledger exactness rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/204_fft_namecert_construction.tex`

Rationale:
204_fft_namecert_construction.tex (175 lines) has 5 abstract theorems (butterfly obligation, factorization stability, ledger exactness, threshold unblock, public NameCert export) but no boundary-instance result. grep for `FFT.*length|FFT.*single|FFT.*size.*one|FFT.*identity` returns zero. The length-one DFT-equals-input row is the single most basic concrete FFT instance and is exactly the kind of boundary-cardinality theorem the loop has produced for sibling areas (cf. B-538 Quadrature empty-node sum is zero, B-575 Quadrature singleton-node sum, B-553 Zero-spine source shape exhaustion). FFT is missing this slot. File at 175/800.

---

### B-642 - BilinFormUp pairing of the zero vector with any carried partner classifies with the zero scalar

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | BilinFormUp pairing of the zero vector with any carried partner classifies with the zero scalar |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For an accepted BilinFormUp pairing of \autoref{def:bilinform-module-pairing-source-row} on a module-and-vector-space source, every carried right vector-source row y satisfies BilinPair_{B}(0_V, y, ν) classified with the scalar zero endpoint, read through the bilinearity transport row \autoref{thm:bilinform-bilinearity-transport-row} alone.

Local inputs:
- `papers/bedc/parts/concrete_instances/124_bilinform_namecert_construction.tex`

Rationale:
124_bilinform_namecert_construction.tex (343 lines) has 14 theorems including bilinearity transport, dual symmetry, nondegeneracy ledger, and root rows. The forward direction `B(0_V, y) = 0_K` (an immediate consequence of left-additivity at 0 + 0 = 0) is missing — the file only contains the *converse* nondegeneracy readback (lines 233, 319) saying `if pairing ends at zero for all partners, then x is the zero vector`. The forward zero-vector vanishing row is a strictly weaker single-implication and a standard preliminary used by Clifford/InnerProduct downstream. No completed BOARD entry on bilinform vanishing; closest is B-583 CliffordUp polarization. File at 343/800.

---
