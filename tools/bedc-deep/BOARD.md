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

### B-659 - Bundle-local same-source gap memberships share signatures

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Bundle-local same-source gap memberships share signatures |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
If BundleAskPolicy(Π,D) holds and InGapSig(Π,D,p,h) and InGapSig(Π,D,q,h), then there exist generated signatures s,t introducing p,q with hsame(s,t).

Local inputs:
- `papers/bedc/parts/concrete_hardening/internalized_gap_globalize.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
internalized_gap_globalize.tex:86 states thm:gap-memberships-share-signature under AskPol(Π,D); the proof uses only signature determinacy on a shared admitted source, which has a bundle-local form at probe_bundles/02_signature_generation.tex:365 (thm:bundle-local-signature-determinacy). This is the witness-extraction sibling of B-646 — that target strengthened the closing psame step; this one strengthens the intermediate signature-witness extraction that feeds it. No theorem named `bundle-local-share-signature` or with BundleAskPolicy as premise for this witness-form claim exists (grep on parts/). The Lean side `inGapSig_same_source_package_witnesses` (line 96) is AskPol-only; no bundle-local variant. Distinct claim from gap-separation: it returns existential signature witnesses, not just psame(p,q).

---


### B-660 - Signature append residual exactness with known Θ-component

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Signature append residual exactness with known Θ-component |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Under BundleAskPolicy(Π,D), BundleAskPolicy(Θ,D), PkgPol(BAppend(Π,Θ)), PkgTokPol(BAppend(Π,Θ)), and PkgTokPol(Θ), if the appended interface and the known Θ-component each carry compatible psame on introduced tokens for histories h,k, then sameSig_Π(h,k).

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
package_token_policy.tex:470 states thm:signature-append-residual-known-token-component for the known Π-component direction only (cancels Π, returns sameSig_Θ). The mirror direction (cancel Θ, return sameSig_Π) is not stated. The underlying right-cancellation infrastructure exists: 02_signature_generation.tex:253 has thm:samesig-bundle-append-right-cancellation under BundleAskPolicy(Θ,D), and 02_signature_generation.tex:269 has thm:samesig-bundle-append-residual-iff item (2) covering the Θ-known iff at the sameSig level. The remaining task is to lift that residual iff through the token-introduction layer using psame_iff_hsame, exactly parallel to the existing Π-direction proof. Host file 513 lines, ~50 added still under 760. Genuine mirror gap, not parameter echo: requires invoking BundleAskPolicy(Θ,D) where the existing theorem invokes BundleAskPolicy(Π,D).

---


### B-661 - Token uniqueness from package-token policy on the concrete signature-token instance

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Token uniqueness from package-token policy on the concrete signature-token instance |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If PkgTokPol(Π) holds for the concrete signature-token relation psame_Π^{sig}, then TokUnique(Π): TokIntro(Π,s,p) and TokIntro(Π,t,p) imply hsame(s,t).

Local inputs:
- `papers/bedc/parts/proof_obligations/package_token_policy.tex`
- `papers/bedc/parts/proof_obligations/psame_design.tex`

Rationale:
package_token_policy.tex:360 states thm:package-token-policy-from-token-unique (TokUnique → PkgTokPol) but the converse is not stated. Lean side: `grep 'TokUnique_from|tokUnique_from_packageTokenPolicy' lean4/BEDC/` returns 0 — only `packageTokenPolicy_from_tokUnique` exists. The converse holds: given TokIntro(Π,s,p), TokIntro(Π,t,p), apply soundness with hsame(s,s) to two copies of TokIntro(Π,s,p) yielding psame(p,p); then reflection on TokIntro(Π,s,p), TokIntro(Π,t,p), psame(p,p) gives hsame(s,t). Together with the existing forward direction this gives an equivalence (TokUnique ⇔ PkgTokPol) on the concrete instance — closes the policy-mode contract loop highlighted in def:policy-mode (line 375). Concrete uniqueness claim, host file 513 lines.

---

