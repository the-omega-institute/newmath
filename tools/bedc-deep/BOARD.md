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

### B-657 - Bundle-local internalized gap coverage (companion to bundle-local separation)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Bundle-local internalized gap coverage (companion to bundle-local separation) |
| Layer | concrete_hardening |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Assume BundleAskPolicy(Π,D) and the dependent token condition: whenever InDom(D,h) and Sig(Π,h,s,Δ) there exists p with TokIntro(Π,s,p); if InDom(D,h), then there exists p with InGapSig(Π,D,p,h).

Local inputs:
- `papers/bedc/parts/concrete_hardening/internalized_gap_globalize.tex`

Rationale:
B-646 just landed the bundle-local separation strengthening in the same chapter (papers/bedc/parts/concrete_hardening/internalized_gap_globalize.tex) but the coverage twin thm:gap-coverage-concrete still requires the global AskPol(Π,D). The asymmetry is exactly the kind a referee flags. The chapter is 230 lines (well under the 800 cap), thm:bundle-local-signature-existence already provides the signature totality from BundleAskPolicy, and composing it with the dependent token condition mirrors the existing proof structure for thm:gap-coverage-concrete. Distinct from B-646 (separation, not coverage) and not currently a labeled theorem in the paper index.

---


### B-658 - PackageTokenPolicy reflection reflects to TokUnique (converse of policy-from-token-unique)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | PackageTokenPolicy reflection reflects to TokUnique (converse of policy-from-token-unique) |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
For the concrete signature-token relation, PkgTokPol(Π) implies TokUnique(Π); equivalently, the existing theorem TokUnique ⟹ PkgTokPol upgrades to an iff.

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`

Rationale:
Closes the converse of thm:package-token-policy-from-token-unique (papers/bedc/parts/proof_obligations/package_token_policy.tex:360). The candidate proof uses only PkgTokPol's two existing fields (soundness + reflection on common introductions) and does not introduce new hypotheses. Upgrading the one-sided implication to an iff is structurally important for the policy/uniqueness equivalence story and not duplicated by TokUnique_iff_tokenReplacement (a different equivalence at line 244). Distinct from any active BOARD title and lands inside the existing proof_obligations file without hub or line-cap risk.

---

