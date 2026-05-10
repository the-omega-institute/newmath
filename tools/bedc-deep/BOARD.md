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

### B-616 - CurryHoward cut-beta endpoint classifier reflexivity row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | CurryHoward cut-beta endpoint classifier reflexivity row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
Every accepted shared cut-beta packet H is related to itself by the CurryHoward endpoint classifier of Definition curryhoward-endpoint-classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/243_curryhoward_namecert_construction.tex`

Rationale:
243_curryhoward_namecert_construction.tex (355 lines, 10 theorems) has classifier endpoint transport (line 87), source row separation (line 46), classifier exhaustion (line 135), endpoint exactness (line 179), and proof-program determinacy (line 113) — but no reflexivity statement for the cut-beta endpoint classifier. Other concrete classifier surfaces (RandomVar, FirstOrder, Sheaf) all carry an explicit reflexivity row; CurryHoward is the conspicuous omission. Single-implication form: accepted packet ⇒ classifier H≈H. Within an existing chapter (no Lean axiom), file far below cap, no sibling on BOARD.

---

