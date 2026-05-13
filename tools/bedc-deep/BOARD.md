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

### B-723 - TaylorModel finite jet prefix restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | TaylorModel finite jet prefix restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted TaylorModel carrier has finite jet ledger J and a displayed prefix or subwindow J' of J that preserves the selected coefficient histories and their StreamName windows, then the projected packet over J' is again an accepted finite TaylorModel read surface and every consumer-visible coefficient read factors through J' without accessing coefficients outside J'.

Local inputs:
- `papers/bedc/parts/concrete_instances/1680_taylormodel_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: low, the existing TaylorModel chapter is short and already exposes the finite jet ledger, finite-jet transport, and validated consumer boundary needed for a projection lemma.
Rationale:
This is a concrete finite-ledger closure result inside the existing TaylorModel chapter, not a verification marker or parameter-transport echo. The current paper proves that coefficient reads factor through the whole finite jet ledger, but it does not state the referee-natural restriction property for a displayed prefix or subwindow of that ledger. Existing BOARD entries contain many finite restriction patterns, but none for TaylorModel finite jets, and the local file is well below the line cap with a safe landing path.

---


### B-724 - CauchyFilter finite subfilterbase restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CauchyFilter finite subfilterbase restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted CauchyFilter carrier F=(B,R,M,L,P) has a displayed finite subfamily B' of base packets that is closed under the refinement rows used by R and contains the bases selected by M for the requested precisions, then the projected rows form an accepted CauchyFilter carrier with the same finite downstream handoff boundary.

Local inputs:
- `papers/bedc/parts/concrete_instances/592_cauchyfilter_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: medium, the restriction hypothesis must explicitly preserve all refinement and modulus rows to avoid becoming a vague filter-theoretic claim.
Rationale:
This belongs as a local existing-chapter lemma for the CauchyFilter finite-filterbase surface. The paper currently records the finite carrier, directed refinement obligation, Cauchy modulus obligation, and NameCert surface, but not closure under a displayed finite subfilterbase satisfying the needed refinement and modulus side conditions. It is close to other finite restriction BOARD patterns, so novelty is only threshold-level, but it is not a duplicate of an existing CauchyNet or finite-window target and it has a safe, short landing file.

---

