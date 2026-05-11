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

### B-666 - Bundle-local concrete Globalize classifies-by-signatures

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Bundle-local concrete Globalize classifies-by-signatures |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Assume BundleAskPolicy(Pi,D), PkgTokPol(Pi), InGapSig(Pi,D,p,h), InGapSig(Pi,D,q,k); then psame(p,q) iff there exist s,t,Delta,Theta with Sig(Pi,h,s,Delta) and Sig(Pi,k,t,Theta) and hsame(s,t).

Local inputs:
- `papers/bedc/parts/concrete_hardening/internalized_gap_globalize.tex`
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`

Rationale:
The chapter proves three bundle-local cousins of the AskPol-based theorems: bundle-local-internalized-gap-separation (line 202), bundle-local-internalized-gap-coverage (line 232), bundle-local-gap-memberships-share-signature (line 256). The corresponding AskPol-based classification corollary cor:concrete-globalize-classifies-by-signatures sits at line 155 (uses AskPol+PkgTokPol). Grep for 'bundle.local.*classif|bundleAskPolicy.*classif|bundle.local.*globalize|bundleAskPolicy.*Glob' across papers/bedc/parts/ and lean4/BEDC/ returns 0 — confirming no bundle-local classification corollary exists in either side. The reverse direction reduces to thm:bundle-local-signature-determinacy (papers/bedc/parts/core/probe_bundles/02_signature_generation.tex:365) plus PkgTokPol soundness, both already available. Lands cleanly in internalized_gap_globalize.tex (293 lines, room). Concrete classification claim, not parameter echo.

---

### B-668 - Three-layer composite gap exactness from layered hypotheses

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Three-layer composite gap exactness from layered hypotheses |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If three layers C, D, E each have coverage of their lower carriers (with intermediate admissibility certificates), separation of witnesses up to interSame at each level, and each successor layer transports interSame across its layer's gap, then the threefold composite CompGap(CompGap(C,D),E) (equivalently CompGap(C,CompGap(D,E))) has both coverage and separation.

Local inputs:
- `papers/bedc/parts/core/07_gap_policies_coverage_separation_and_composition.tex`

Rationale:
Theorem thm:composite-exactness-from-layers (papers/bedc/parts/core/07_gap_policies_coverage_separation_and_composition.tex:121) gives the 2-layer composite exactness; no 3-layer version is stated. Grep for 'composite.*three.*layer|three.layer.*exact|threefold.*composite.*exact|3.layer.*composite|composite.*exact.*three' returns only a sheaf-side reference, confirming the abstract gap-level 3-layer exactness is open. Non-trivial because the InterOk admissibility certificate must compose across two intermediate levels, and the inter-same/final-same transport chain must thread through both gap relations. Lands in 07_gap_policies (237 lines, has room). Concrete closure claim about composite predicates under stacked layered hypotheses, not parameter transport.

---
