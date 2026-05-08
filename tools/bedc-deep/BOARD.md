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

### B-550 - Identity pullback gap policy unit law

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Identity pullback gap policy unit law |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
If GapPol(Pi, D), then id_D: D -> D carries a classifier-preserving pullback ledger over Pi and {InGapSig}^{id_D}(Pi, D, D, p, h) <=> InGapSig(Pi, D, p, h) on every admitted history.

Local inputs:
- `papers/bedc/parts/proof_obligations/gap_policy.tex`

Rationale:
Pairs naturally with B-504 (n-fold composite pullback) by supplying the unit element of the same composition operation, completing the monoid structure of classifier-preserving pullback ledgers in proof_obligations/gap_policy.tex. The file already states the binary composite (thm:composite-pullback-gap-policy at lines 197-267) but no identity/unit theorem exists in the file (grep found no 'id_D' / 'unit' / 'identity' occurrences). BOARD precedent supports identity-unit companion theorems in the same lane (B-481 Banach identity units, B-484 QuantumChannel identity composition units, B-520 Sheaf identity refinement, B-391 Quantum channel identity closure), so this is consistent with existing granularity. Proof is largely definitional (source preservation by reflexivity; classifier-preservation iff collapses), which is why fit/novelty are at threshold rather than higher. File is 267 lines, well under the 800-line cap, safe to land.

---

