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

### B-671 - DyadicPrecision empty precision schedule exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | DyadicPrecision empty precision schedule exactness |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If a \DyadicPrecisionUp schedule is generated from the empty unary precision row, then under the schedule carrier its radius row is the base \DyadicRatCoreUp dyadic radius and its \StreamNameUp observation window is empty, with consumer reads exhausted by those two displayed rows and the provenance ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/484_dyadicprecision_namecert_construction.tex`

Rationale:
The carrier explicitly exposes a unary precision row n, a selected dyadic radius rho, a StreamName window W, and a ledger L at papers/bedc/parts/concrete_instances/484_dyadicprecision_namecert_construction.tex:9-26; the NameCert theorem only lists carrier inhabitation and ledger exactness as broad obligations at lines 42-50, while its proof contains the unpromoted boundary sentence that the empty unary row attaches the base dyadic radius and empty observation window at line 55. A focused grep for dyadic empty precision/base radius/empty observation window found only that proof sentence and no labeled theorem, and the file-level theorem inventory shows only thm:dyadic-precision-schedule-namecert-obligations, thm:dyadic-precision-schedule-regseqrat-handoff, and thm:dyadic-precision-schedule-realup-boundary at lines 42-75. Marker grep on this file returned 0 Lean markers, and find/ls for lean4/BEDC names matching DyadicPrecision returned 0 files, so this is not already a Lean-linked or hidden labeled theorem.

---


### B-672 - NestedDyadicInterval singleton chain vacuity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | NestedDyadicInterval singleton chain vacuity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If an accepted \NestedDyadicIntervalUp carrier displays exactly one interval row, then under the finite-chain carrier its nested-refinement ledger has no successor-pair reads and its public handoff is exactly that interval, the schedule, provenance, and tail ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/527_nesteddyadicinterval_namecert_construction.tex`

Rationale:
The carrier defines K=(I_0,\ldots,I_n,S,R,P,L), with R storing a refinement row for every displayed successor pair and L hiding only the unobserved tail, at papers/bedc/parts/concrete_instances/527_nesteddyadicinterval_namecert_construction.tex:9-23. Existing theorems cover endpointwise window transport, RegSeqRat handoff, and the NameCert surface at lines 33-79, but none isolates the zero-successor-pair case. A focused grep for NestedDyadicInterval singleton/single/vacuous/one displayed and matching theorem labels returned 0 hits across papers/bedc/parts and lean4/BEDC. The exact local theorem inventory contains only thm:nesteddyadicinterval-window-transport, thm:nesteddyadicinterval-regseqrat-handoff, and thm:nesteddyadicinterval-namecert-obligation-surface at lines 33-62; marker grep on this file returned 0 Lean markers, and find/ls for lean4/BEDC names matching NestedDyadic returned 0 files.

---


### B-673 - BousfieldLocalization empty selected-map boundary

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | BousfieldLocalization empty selected-map boundary |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If an accepted \BousfieldLocalizationUp carrier has an empty selected morphism-class row S, then under the finite localizing packet every inverted-map consumer read is absent and downstream handoff is limited to M, L, T, P, and N rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/492_bousfieldlocalization_namecert_construction.tex`

Rationale:
The carrier defines B=(M,S,L,T,P,N), with S as the finite selected morphism-class row and L as fibrant-local-object rows, at papers/bedc/parts/concrete_instances/492_bousfieldlocalization_namecert_construction.tex:11-27. Existing theorems state broad NameCert obligations and a local-object handoff where consumers read local-object rows in L and selected maps in S at lines 29-63, but they do not spell out the empty-S boundary or the absence of inverted-map reads. A focused grep for BousfieldLocalization empty selected/no selected/empty morphism/empty map and matching theorem labels returned 0 hits across papers/bedc/parts and lean4/BEDC. The exact local theorem inventory contains only thm:bousfieldlocalization-namecert-obligations and thm:bousfieldlocalization-local-object-handoff at lines 29-52; marker grep on this file returned 0 Lean markers, and find/ls for lean4/BEDC names matching Bousfield returned 0 files.

---


### B-674 - FiniteVector empty length has no component reads

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | FiniteVector empty length has no component reads |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 7/10 |

Problem:
If an accepted \FiniteVectorUp carrier has displayed NatUp length zero, then under the finite-vector carrier its ProdUp index-component spine has no public index-component pair rows and classifier comparison reduces to length, empty spine, provenance, and outside-length ledger rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/531_finitevector_namecert_construction.tex`

Rationale:
The carrier states that n is the NatUp length row, L is the component spine with displayed length n, I has one ProdUp index-component row for each visible index below n, and H hides only positions outside the displayed length at papers/bedc/parts/concrete_instances/531_finitevector_namecert_construction.tex:9-25. Existing theorems cover length-index stability, componentwise ledger exactness, and the NameCert surface at lines 41-91, but not the zero-length boundary where the index set is empty. A focused grep for FiniteVector empty length/zero length/empty vector/no component and theorem labels found only the existing generic thm:finitevector-length-index-stability references at lines 42, 76, and 86, with no empty/zero theorem. Marker grep on this file returned 0 Lean markers, and find/ls for lean4/BEDC names matching FiniteVector returned 0 files; the file is only 104 lines, so it is a suitable child target rather than a hub or near-cap file.

---

