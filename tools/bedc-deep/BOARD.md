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

### B-675 - S1 completion-readback injectivity prerequisite

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (both) |
| Object | S1 completion-readback injectivity prerequisite |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
Under the visible S1 carrier/readback setup, if a cancellative additive source map is injective and the bridge reads a displayed completion representative, then source separation is preserved by the completion readback without using host quotient primitives.

Local inputs:
- `papers/bedc/parts/concrete_instances/s1/carrier_readbacks.tex`

Rationale:
This is a concrete bridge-prerequisite target that lands on the existing S1 carrier/readback surface rather than importing a host completion object. It is distinct from the current S1 transport, determinacy, public readback, and constructor-compatibility rows, and it is not present in the existing BOARD title index or paper labels. The landing file is not a hub and is below the line cap, so the target can be staged safely as a local theorem/proposition about visible representatives and separation.

---

### B-676 - S1 finite-rank host homologization obstruction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | S1 finite-rank host homologization obstruction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
Under the S1 carrier/readback bridge setup, if a finite-rank host homologization certificate is admitted for the visible S1 bridge ledger, then the induced bounded-rank certificate is incompatible with cofinal prime-support evidence, so the finite-rank host homologization is obstructed.

Local inputs:
- `papers/bedc/parts/concrete_instances/s1/carrier_readbacks.tex`

Rationale:
This is a concrete obstruction target over the existing S1 carrier/readback surface rather than a marker-only or verification-axis task. It is distinct from the active S1 completion-readback injectivity prerequisite: B-675 concerns preservation of source separation through displayed completion readbacks, while this candidate asks for an obstruction to a finite-rank host homologization certificate using bounded-rank versus cofinal-support evidence. The local input is not listed as a hub file or near the 800-line cap, and the claim can be staged as a BEDC-native bridge-obligation theorem without importing Automath runtime state.

---

### B-677 - S1 boundary-readback Cayley coordinate certificate

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (codex) |
| Object | S1 boundary-readback Cayley coordinate certificate |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
Under the S1 boundary-readback setup, if BEDC has a named S1 readback carrier for the Cayley coordinate and the Automath Cayley coordinate/inverse evidence supplies the coordinate laws, then the displayed S1 boundary readback carries the Cayley coordinate certificate row.

Local inputs:
- `papers/bedc/parts/concrete_instances/s1/carrier_readbacks.tex`

Rationale:
This is an evidence-backed bridge continuation with a plausible BEDC-native landing surface: the existing S1 carrier/readback file is already the active locus for S1 bridge/readback targets, and this candidate asks for one concrete certificate row rather than analytic boundary theory. It is distinct from B-675, which is about completion-readback injectivity preservation, and B-676, which is about finite-rank host homologization obstruction. Provenance must be preserved: Automath source the-omega-institute/automath@origin/dev, commit aecb76a5a5eed83cc6bdbb981b51ebfb58dd695f, source path papers/publication/2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa/sec_cayley_gate.tex, evidence packet tools\automath_newmath_bridge\review_packets\papers-publication-2026-cayley-chebyshev-poisson-entropy-strip-rkhs-jfa-sec-cayley-gate-tex-ce39cd0cc9a6.json, source labels sec:cayley-gate, eq:phase-coord, eq:angular-var, eq:cayley-embed, prop:cayley-homeo, eq:cayley-inverse. Reuse instruction: inspect and consume existing Automath evidence first; do not rediscover or re-prove the Automath theorem unless BEDC needs a native restatement. Expected NewMath delta: one S1 boundary-readback Cayley coordinate certificate row or a rejected BEDC-fit note. Reject if no S1 boundary-readback carrier or name-certificate host can represent the Cayley coordinate.

---

