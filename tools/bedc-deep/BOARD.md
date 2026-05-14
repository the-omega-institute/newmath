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

### B-749 - FieldExt downstream dependency lattice exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | FieldExt downstream dependency lattice exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_ledger_row |

Problem:
If a downstream Galois, NumField, separability, algebraic-closure, or tower consumer consumes a FieldExtUp packet, then every accepted read factors through the displayed base FieldUp row, ambient FieldUp row, VecSpaceUp-over-base row, embedding row, and local FieldExtUp naming ledger.

Local inputs:
- `papers/bedc/parts/concrete_instances/fieldext/sibling_dependency_lattice.tex`
- `papers/bedc/parts/concrete_instances/fieldext/intro_singleton_embedding.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: cut_rank 0: prove by direct projection from the displayed FieldExtUp dependency lattice and repacking of the two FieldUp endpoint rows, the VecSpaceUp-over-base row, the embedding row, and the local ledger, with no intermediate ambient tower object.
- `ripeness_risk`: low, the cited landing files are short child files and the sibling dependency lattice already states the exact finite row surface in prose.

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The target only consumes a fixed finite packet of displayed rows and forbids an extra ambient tower coordinate, so no schedule, modulus, cover, countable construction, quotient, or choice-like principle is visible.
- `witness_extractor`: Projection of the five displayed lattice components: base FieldUp endpoint, ambient FieldUp endpoint, VecSpaceUp-over-base row, embedding row, and local FieldExtUp naming ledger.
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `elimination_plan`: cut_rank 0: prove by direct projection from the displayed FieldExtUp dependency lattice and repacking of the two FieldUp endpoint rows, the VecSpaceUp-over-base row, the embedding row, and the local ledger, with no intermediate ambient tower object.
- `equality_kind`: none
- `interpretation_kind`: none
- `resource_trace`: A finite consumer packet over two FieldUp endpoints, one VecSpaceUp-over-base row, one embedding row, and the local FieldExtUp naming ledger.
- `dependency_trace`: sec:fieldext-sibling-dependency-lattice; def:fieldext-singleton-empty-history-instance; def:fieldext-singleton-obligation-scope; thm:fieldext-singleton-certificate-obligation-package; thm:fieldext-ratup-reflexive-certificate-row-exhaustion.
- `oracle_mode`: rewrite_to_packet
Rationale:
This is a concrete existing-chapter ledger row rather than a new object: the FieldExt chapter already exposes singleton and RatUp-reflexive FieldExt packages, and the sibling dependency lattice explicitly says downstream Galois, number-field, separability, algebraic-closure, and tower consumers must read through the displayed horizontal lattice instead of an ambient tower object. Existing theorem labels cover endpoint exactness, tower composition, source-pattern locks, and certificate row exhaustion, but no theorem-like paper label closes the downstream non-escape lattice itself. The target is therefore narrow, BEDC-native, finite, and distinct enough to merit a BOARD slot.

---

