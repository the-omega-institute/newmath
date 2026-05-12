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

### B-695 - Singleton-probe sameSig exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Singleton-probe sameSig exactness |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under the singleton bundle setup, for histories h and k, sameSig_{Bcons(π,Bnil)}(h,k) holds if and only if there exist Ask(π,h,m,δ) and Ask(π,k,n,θ) with msame(m,n).

Local inputs:
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
This is a concrete core signature-classification theorem rather than a verification marker or closure-status task. Existing core coverage includes singleton bundle grammar, empty-bundle sameSig, cons signature inversion/determinacy, sameSig append closure/cancellation/exact split, and duplicate-probe obstruction, but no paper label or BOARD title states the one-probe exact iff reducing singleton signature sameness precisely to the two head Ask events and mark sameness. It is close to the signature-generation surface yet distinct from append residual and cons determinacy results, and the proposed landing files are not hub-only and remain below the line cap for a short theorem insertion.

---

