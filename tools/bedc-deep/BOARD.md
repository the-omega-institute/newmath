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

### B-693 - ValidatedNumerics refinement composition

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ValidatedNumerics refinement composition |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If an accepted ValidatedNumericsUp packet refines to a second packet and the second refines to a third while preserving the displayed enclosure, modulus, observation window, readback token, transports, and containment routes, then the composite refinement still routes every displayed approximation into the original finite enclosure row.

Local inputs:
- `papers/bedc/parts/concrete_instances/1042_validatednumerics_namecert_construction.tex`

Rationale:
The ValidatedNumerics chapter has a one-step precision refinement containment theorem and separate containment-ledger transport, but no explicit two-step refinement composition theorem. The proposed target is a concrete closure result for a natural downstream consumer operation, expressible as a single implication over the existing packet coordinates and Cont/hsame ledger rows. It is distinct from the existing one-step result and lands in a non-hub file well below the line cap.

---
