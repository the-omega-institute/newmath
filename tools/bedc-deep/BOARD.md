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

### B-647 - AffineSpaceUp inverse-vector action cancels back to the carried point

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AffineSpaceUp inverse-vector action cancels back to the carried point |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Let p be a carried point row and v be an accepted vector row whose translation reading is accepted by the GroupUp dependency; then act(act(p,v), -V v) and p admit AffineSpace repackings classified by AffCls over the same source certificates.

Local inputs:
- `papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex`

Rationale:
184_affinespace_namecert_construction.tex (230 lines) has 'AffineSpaceUp action additivity' at line 189 (= B-510) and 'AffineSpaceUp zero action classifies the carried point' at line 212 (= B-571). Combining them gives act(act(p,v),-v) ~ act(p, v +V (-v)) ~ act(p, 0V) ~ p, but no theorem exposes this two-step cancellation. Grep 'inverse.*vector|negative.*vector|act.*inv' in the file returns only proof prose at line 119 mentioning 'inverse translation packet supplied by the GroupUp certificate' — used internally for free-action argumentation, never as a top-level row. This is a concrete inversion claim about the action pair (v,-v); not parameter-transport because the proof requires combining additivity, zero-action, and the GroupUp inverse law for the translation-packet readings. File at 230 lines.

---
