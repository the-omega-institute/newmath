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

### B-685 - FiniteMap displayed support readback

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | FiniteMap displayed support readback |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If an accepted FiniteMapUp source is read through a FinSetUp support boundary, then the support row is exactly the displayed key rows in the ListUp spine, with duplicate keys retained as ledger entries rather than extra first-hit lookup outputs.

Local inputs:
- `papers/bedc/parts/concrete_instances/775_finitemap_namecert_construction.tex`

Rationale:
This is a concrete BEDC instance-level readback theorem, not a marker or verification-axis task. The FiniteMap chapter explicitly uses finite support through FinSetUp in its story and closure surface, while the labelled theorem surface currently covers the carrier/classifier obligations, lookup Option exactness, ledger transport, and the NameCert obligation surface. The proposed target isolates the support-boundary projection that is mentioned but not separately closed, and it is distinct from existing BOARD entries and from the existing FiniteMap labels.

---


### B-686 - RegularLanguage empty-word acceptance exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | RegularLanguage empty-word acceptance exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 7/10 |
| Novelty | 6/10 |

Problem:
If an accepted RegularLanguageUp packet has the empty ListUp input spine, then its accepted endpoint row is exactly the start-state row together with membership of that start state in the accepting-state carrier F.

Local inputs:
- `papers/bedc/parts/concrete_instances/692_regularlanguage_namecert_construction.tex`

Rationale:
This is a focused empty-spine inversion for an existing concrete instance. The RegularLanguage chapter already states the deterministic empty-word endpoint and separately states accepted-word endpoint transport, but there is no closely matching labelled theorem that packages the empty-word accepted endpoint itself as start-state plus accepting-carrier membership. The claim is narrow, concrete, lands in the existing chapter without hub or line-cap risk, and is sufficiently distinct from existing BOARD entries.

---

