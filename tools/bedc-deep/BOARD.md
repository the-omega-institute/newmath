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

### B-721 - Signature append cut decomposition uniqueness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Signature append cut decomposition uniqueness |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If BundleAskPolicy(Pi,D), BundleAskPolicy(Theta,D), h is admitted by D, and Sig(BAppend(Pi,Theta),h,u,Lambda) has two append-inversion decompositions with component results (s,t) and (s',t'), then hsame(s,s') and hsame(t,t').

Local inputs:
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`

Rationale:
This lands as a small core lemma next to the existing signature append generation, inversion, decomposition, and component-determinacy theorems. It is close to the established append-splitting surface, so novelty is only threshold-level, but it states a distinct fixed-source uniqueness property for two recovered cut pairs rather than an existence decomposition or a sameSig comparison between two sources. The local files are ordinary content files under the line cap and the target can be expressed as a single deterministic implication under the existing bundle-local policy hypotheses.

---
