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

### B-703 - FoldMomentKernel finite-window restriction carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | FoldMomentKernel finite-window restriction carrier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If an accepted FoldMomentKernel packet is restricted to a displayed finite subwindow and the fold-source, fiber-ledger, moment-index, collision-count, transport, continuation, provenance, and local NameCert rows restrict coherently, then the restricted packet is again an accepted FoldMomentKernel carrier.

Local inputs:
- `papers/bedc/parts/concrete_instances/1289_foldmomentkernel_namecert_construction.tex`

Rationale:
The candidate is a concrete closure theorem over an existing concrete-instance surface, not a marker, closurestatus, verification-axis item, or abstract parameter echo. It has a single implication form, lands naturally in the FoldMomentKernel NameCert construction, and the proposed input is not identified as a hub file or near the 800-line cap. Existing BOARD entries contain many analogous finite-prefix, finite-suffix, and finite-window carrier restrictions for other instances, but no FoldMomentKernel-specific target, so this is familiar in shape while still novel as a concrete object-level closure target.

---

