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

### B-663 - Append sameSig exact split into both components

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Append sameSig exact split into both components |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under BundleAskPolicy(Π,D), BundleAskPolicy(Θ,D), and h,k admitted by D, sameSig_{BAppend(Π,Θ)}(h,k) implies sameSig_Π(h,k) and sameSig_Θ(h,k).

Local inputs:
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`

Rationale:
B-660 covers residual exactness with a known Θ-component; B-659 covers bundle-local same-source membership sharing signatures. Neither gives the unconditional component-split converse to append closure of sameSig. This is the appended-classifier → two-component-classifiers exact split, a genuine converse of the append closure theorem rather than a paraphrase. Lands cleanly in 02_signature_generation.tex.

---

### B-665 - Second-layer separation is necessary for composite gaps

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Second-layer separation is necessary for composite gaps |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
There exists a finite CompGap setup with firstGap coverage+separation and secondGap coverage but not separation such that the same source falls into composite gaps of two distinct final tokens with finalSame failing.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`

Rationale:
Existing ledger composition theorems give the forward direction (first+second separation ⇒ composite separation). The paper currently does not record a witness/obstruction showing second-layer separation cannot be weakened. A concrete two-point witness on b0,b1 final tokens with finalSame=msame closes a genuine gap and converts a sufficient-condition theorem into a tight one. High-novelty obstruction target, fits the proof_obligations layer exactly.

---
