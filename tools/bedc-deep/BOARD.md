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

### B-732 - AuditMapFrontierIndex neighbor restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AuditMapFrontierIndex neighbor restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If an accepted AuditMapFrontierIndexUp packet restricts its neighbouring-map row to a displayed finite subfamily while retaining the local audit row, positive rows, conditional route row, obstruction row, frontier row, synthesis-consumer row, transports, continuations, provenance, and local NameCert rows for that subfamily, then the restricted packet is an accepted frontier index and no unlisted neighbouring map can supply a frontier entry.

Local inputs:
- `papers/bedc/parts/concrete_instances/4518_auditmapfrontierindex_namecert_construction.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: Project the neighbouring-map row to the displayed finite subfamily and restrict the positive, conditional-route, obstruction, frontier, synthesis-consumer, transport, continuation, provenance, and local NameCert rows to the retained entries.
- `ripeness_risk`: low, the source chapter is a finite frontier-index carrier and the proposed theorem is a direct finite-subfamily locality statement

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The weakest visible resource is a finite witness because the theorem only projects a displayed neighbouring-map row and repacks retained finite certificate coordinates.
- `witness_extractor`: frontier_neighbor_subfamily_projection
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Project the neighbouring-map row to the displayed finite subfamily and restrict the positive, conditional-route, obstruction, frontier, synthesis-consumer, transport, continuation, provenance, and local NameCert rows to the retained entries.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: conservative_extension
- `resource_trace`: Consumes T,A,E,P,R,O,F,S,H,C,K,N with E restricted to a displayed finite neighbouring-map subfamily and all frontier, obstruction, route, consumer, transport, continuation, provenance, and NameCert rows retained only for that subfamily.
- `dependency_trace`: Uses def:audit-map-frontier-index-carrier and thm:audit-map-frontier-index-namecert-obligations in papers/bedc/parts/concrete_instances/4518_auditmapfrontierindex_namecert_construction.tex.
- `oracle_mode`: proof_search
Rationale:
This is a concrete finite-subfamily restriction theorem inside an existing audit-map frontier chapter. It is not already covered by the carrier or the five NameCert obligations: those bind the frontier index and synthesis handoff, but do not explicitly state locality under displayed neighbouring-map restriction or the corresponding no-unlisted-neighbour non-escape result. The file is a short non-hub landing, so it is safe as an existing-chapter lemma.

---
