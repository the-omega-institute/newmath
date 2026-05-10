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

### B-635 - BusyBeaver per-machine halted-readback determinism on empty tape

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | BusyBeaver per-machine halted-readback determinism on empty tape |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If two accepted BusyBeaverUp witnesses share a finite enumeration E and both record a halted branch for the same entry M in E, then their halted output rows, step-count rows, and finite TuringMachineUp transition traces from the empty tape are hsame-equal in the carrier ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/264_busybeaver_namecert_construction.tex`

Rationale:
Genuine no-confusion gap. The chapter premises deterministic Turing-machine codes (264:9) and the existing thm:busybeaver-per-machine-readback-exactness only reads back one accepted packet. The deterministic-code hypothesis should force any two halted branches for the same M to agree on output, step count, and transition trace — but no current theorem makes that comparison. Fits the determinism/uniqueness keeper category cleanly: not a parameter echo of bound monotonicity (264:70-96) or of the non-halting exclusion row (264:99-125). Landing file is 197 lines, far below the cap, with a clear sibling slot adjacent to the existing readback-exactness theorem.

---

