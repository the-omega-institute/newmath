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

### B-694 - Duplicate-probe signature contraction obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Duplicate-probe signature contraction obstruction |
| Layer | core |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If Sig(Bcons(pi,Bcons(pi,Pi)),h,r,Delta) and Sig(Bcons(pi,Pi),h,s,Gamma), then not hsame(r,s).

Local inputs:
- `papers/bedc/parts/core/probe_bundles/01_bundle_grammar.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
This is a concrete obstruction target inside the probe-bundle signature surface: repeated probes may be contracted at a policy-reading level, but generated signature histories cannot be contraction-invariant because result length tracks bundle length. Existing BOARD and paper coverage include empty-result, cons inversion, append residual, and length exactness results, but not this explicit no-contraction obstruction. The target is sharply local, non-marker, non-closurestatus, and lands in non-hub core probe-bundle files below the line cap.

---

