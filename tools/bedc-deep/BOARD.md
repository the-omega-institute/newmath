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

<<<<<<< Updated upstream
=======
### B-704 - AscoliModulus empty-family vacuity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AscoliModulus empty-family vacuity |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under the AscoliModulus carrier setup, if an accepted packet has an empty finite family ledger and an empty source-net probe bundle, then its finite-net stability and family-wide equicontinuity ledgers are vacuous and the Arzela-Ascoli handoff exports only the displayed tolerance, radius, transport, package, and local naming rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/1720_ascolimodulus_namecert_construction.tex`

Rationale:
The candidate is a concrete finite-ledger boundary theorem inside an existing concrete_instances chapter, not a marker or verification-axis task. The current AscoliModulus surface has carrier, equicontinuity ledger, finite-net stability, NameCert obligations, rational-radius transport, family transport, and Arzela-Ascoli handoff theorems, but no theorem isolating the empty family and empty probe-bundle base case. It exposes a useful vacuity boundary for a finite modulus package while preserving the chapter's non-compactness and no-subsequence-choice discipline, and the landing file is well below the line cap.

---


### B-705 - UniformCauchyCriterion empty-family tail ledger

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | UniformCauchyCriterion empty-family tail ledger |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
Under the UniformCauchyCriterion carrier setup, if an accepted packet has an empty finite family index ledger and an empty tail-comparison ledger, then the shared-threshold route is accepted vacuously and the RealUp seal handoff exports no completed family limit or indexwise schedule.

Local inputs:
- `papers/bedc/parts/concrete_instances/1711_uniformcauchycriterion_namecert_construction.tex`

Rationale:
The candidate is a single implication about a concrete finite-family tail-bound surface already present in the UniformCauchyCriterion chapter. Existing theorems cover window stability, RealUp seal handoff, non-escape, tail-ledger exactness, shared-threshold transport, RegSeqRat tail equivalence, obligation assembly, and finite-family window exhaustion, but they do not name the empty-index and empty-tail-ledger boundary as its own base case. The theorem would make the tail-bound and seal-export discipline smaller and easier to cite without adding host completeness, selected limits, or quotient stream equality, and the file is safe for direct landing.

---

### B-706 - DomainPolicy finite Boolean closure

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | DomainPolicy finite Boolean closure |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
Under DomainPolicy(D0) and DomainPolicy(D1), if the compound domains define InDom(D_and,h) as InDom(D0,h) and InDom(D1,h), and InDom(D_or,h) as InDom(D0,h) or InDom(D1,h), then both D_and and D_or satisfy DomainPolicy.

Local inputs:
- `papers/bedc/parts/proof_obligations/domain_policy.tex`

Rationale:
This is a concrete closure theorem for the existing DomainPolicy transport surface, not a marker or verification-axis task. The current paper records DomainPolicy, transport, invariance, three-history transport, and the UnarySource instance, but does not appear to record finite meet/join closure for compound domains. It is distinct from the existing ExactGlobalizeBase subdomain base-change target because it concerns preservation of the domain-policy obligation under Boolean domain constructors rather than restricting an already-globalized base. The landing file is not a hub and is well below the line cap.

---

>>>>>>> Stashed changes
