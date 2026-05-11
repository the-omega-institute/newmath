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

### B-650 - PersistentHomUp empty filtration spine yields empty persistence ledger

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | PersistentHomUp empty filtration spine yields empty persistence ledger |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If an accepted PersistentHomUp carrier packet has its finite filtration-index spine row empty, then its stagewise SimplicialComplexUp readback rows, HomologyUp readback rows, persistence-map ledger entries, and barcode-summary rows are all empty.

Local inputs:
- `papers/bedc/parts/concrete_instances/217_persistenthom_namecert_construction.tex`

Rationale:
PersistentHomUp (217_persistenthom_namecert_construction.tex, 138 lines) has 0 completed BOARD entries and the file's filtration carrier (thm:persistenthom-carrier-obligation-surface, lines 9-34) and ledger exactness (thm:persistenthom-filtration-ledger-exactness, lines 86-108) explicitly enumerate index spine, stage rows, persistence maps, and barcode summary as the only ledger contents — but no theorem witnesses the empty-spine boundary. The pattern matches B-640 (MatroidUp empty-subset), B-630/B-632 (Markov/Brownian finite-suffix restriction), B-638-style boundary lemmas, but the topological-data-analysis subarea is otherwise entirely untouched by the bedc-deep loop.

---


### B-651 - InterpolationUp empty node selection has empty evaluation ledger

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InterpolationUp empty node selection has empty evaluation ledger |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If the FinSetUp selected-node membership ledger of an accepted InterpolationUp carrier row has no entries, then the carrier's polynomial-evaluation ledger contains no sample rows and the sample-ledger surface is empty.

Local inputs:
- `papers/bedc/parts/concrete_instances/202_interpolation_namecert_construction.tex`

Rationale:
InterpolationUp (202_interpolation_namecert_construction.tex, 188 lines) has 0 completed BOARD entries. Its carrier (def:interpolation-bhist-node-carrier, lines 13-32) is explicitly node-indexed, and thm:interpolation-sample-ledger-surface (lines 34-65) reads every accepted sample through one FinSet membership row. Numerical-analysis concept tier (interpolation, quadrature, fft) is partially covered (B-538/B-575/B-590/B-606 quadrature; B-641 fft) but interpolation is missing this baseline empty-index lemma.

---


### B-652 - KalmanFilterUp zero-gain update gives posterior estimate hsame predicted estimate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | KalmanFilterUp zero-gain update gives posterior estimate hsame predicted estimate |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If the gain row K of an accepted KalmanFilterUp carrier packet is hsame to the zero MatrixUp row, then the posterior-estimate row is hsame to the predicted-estimate row of the same packet.

Local inputs:
- `papers/bedc/parts/concrete_instances/272_kalmanfilter_namecert_construction.tex`

Rationale:
KalmanFilterUp (272_kalmanfilter_namecert_construction.tex, 114 lines) has 0 completed BOARD entries. The prediction-update obligation (thm:kalmanfilter-prediction-update-obligation, lines 25-34) exposes a gain row K and posterior-update row, and thm:kalmanfilter-estimate-transport-stability (lines 60-69) gives hsame transport across them — but no zero-gain absorbing-step lemma. Control/estimation subarea (Kalman, LQR, KKT, ControlObservability, ControlControllability) is uniformly at 0 hits in the loop, so this concrete cancellation lemma opens a new front in a well-defined dependency cluster.

---


### B-653 - ControlObservabilityUp zero state-dimension gives empty observation row sequence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ControlObservabilityUp zero state-dimension gives empty observation row sequence |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If the finite-dimensional state-space row of an accepted ControlObservabilityUp carrier packet has dimension zero (n = 0), then the finite observation rows C, CA, \dots, CA^{n-1} form the empty sequence and the stacked observation-matrix row \mathcal O(A,C) has no entries.

Local inputs:
- `papers/bedc/parts/concrete_instances/271_controlobservability_namecert_construction.tex`

Rationale:
ControlObservabilityUp (271_controlobservability_namecert_construction.tex, 92 lines) has 0 completed BOARD entries. The carrier (def:control-observability-carrier, lines 9-21) lists the n-indexed observation rows and stacked \mathcal O(A,C) explicitly, and thm:control-observability-kernel-separation (lines 53-65) reasons about non-degenerate kernels — but the degenerate dimension-zero boundary is not on the surface. Same control-theory cluster gap as #4.

---


### B-654 - LQRUp empty horizon row has empty backward-DP ledger

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | LQRUp empty horizon row has empty backward-DP ledger |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If the finite horizon unary index row of an accepted LQRUp carrier packet is the empty index row, then the Riccati / backward-dynamic-programming ledger contains no update entries.

Local inputs:
- `papers/bedc/parts/concrete_instances/272_lqr_namecert_construction.tex`

Rationale:
LQRUp (272_lqr_namecert_construction.tex, ~183 lines) has 0 completed BOARD entries. def:lqr-finite-control-carrier (lines 9-15) and thm:lqr-dynamic-programming-row (lines 47-58) tie every backward-update Cont row to a finite horizon index; the empty-horizon degenerate case is not on the surface. Together with #4 and #6 this opens three coordinated lemmas in the control cluster (DynSystem dependency neighbourhood), matching the under-covered pattern.

---

