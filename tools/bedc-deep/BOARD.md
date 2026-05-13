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

### B-722 - KernelAcceptanceBuildReplay replay-route determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | KernelAcceptanceBuildReplay replay-route determinacy |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_obligation |

Problem:
For accepted KernelAcceptanceBuildReplay carriers, agreement on the displayed route coordinate and rows G,A,B,S,Q,H,P,N implies that replay consumers reach the same build-command row, replay-result row, and axiom-query handoff row.

Local inputs:
- `papers/bedc/parts/concrete_instances/4010_kernelacceptancebuildreplay_namecert_construction.tex`

Rationale:
This is a concrete finite-packet determinacy obligation inside an existing concrete_instances chapter. The current chapter defines the generated-candidate, accepted-declaration, build-command, replay-result, axiom-query handoff, transport, route, provenance, and naming rows, and its closure upgrade path explicitly names replay-route determinacy as a missing obligation. It is not a marker-only or closurestatus task, the landing file is short and safe, and the target is distinct from existing BOARD entries because it localizes replay-route determinacy to the KernelAcceptanceBuildReplay packet rather than restating generic kernel audit witness or axiom-query ledger non-escape.

---

