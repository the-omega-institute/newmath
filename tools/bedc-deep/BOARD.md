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

### B-548 - CurryHoward cut-beta bridge obligation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CurryHoward cut-beta bridge obligation |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If a CurryHowardUp packet pairs a FirstOrderUp deduction ledger with a LambdaCalcUp term packet through a shared proof-program carrier, then a displayed cut-elimination step on the deduction side is carried to a beta-reduction/substitution ledger on the LambdaCalc side under the shared classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/243_curryhoward_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/175_firstorder_namecert_construction.tex`
- `papers/bedc/parts/concrete_instances/178_lambdacalc_namecert_construction.tex`

Rationale:
This is a concrete bridge obligation between the existing FirstOrderUp deduction-ledger surface and the LambdaCalcUp beta/substitution ledger surface, not the broad capstone observation that Curry-Howard is built into closure laws. The concrete CurryHowardUp chapter is empty, the relevant dependency theorems are already present, and no BOARD entry or paper label states this cut-to-beta bridge. The short CurryHowardUp file is a safe landing point for the bounded theorem.

---
