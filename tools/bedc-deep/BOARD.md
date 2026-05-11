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

### B-681 - GeneratedSameSig append closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | GeneratedSameSig append closure |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If GeneratedSameSig(Π,h,k) and GeneratedSameSig(Θ,h,k), then GeneratedSameSig(BAppend(Π,Θ),h,k).

Local inputs:
- `papers/bedc/parts/proof_obligations/exact_globalize.tex`
- `papers/bedc/parts/core/probe_bundles/02_signature_generation.tex`

Rationale:
This lifts the existing core append closure for sameSig to the checker-facing GeneratedSameSig witness layer consumed by exact Globalize. It is a concrete closure target with downstream proof utility, not a duplicate of the core sameSig append theorem because the conclusion is at the witness-object interface. The proposed files are not hubs and are below the 800-line cap.

---
