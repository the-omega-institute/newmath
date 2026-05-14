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

### B-738 - MetaCIC betasubstitutionpreservation discharge obligation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MetaCIC betasubstitutionpreservation discharge obligation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_obligation |

Problem:
If the MetaCIC subject-reduction discharge interface is used, then the BetaSubstitutionPreservation row is an explicit finite setup obligation required by the interface.

Local inputs:
- `papers/bedc/parts/visions/metacic_open_problems.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: medium, the obligation is clear but should be stated only as a setup requirement, not as an unconditional subject-reduction theorem

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The visible packet is a finite named setup row for one beta-redex preservation case, with no limit, compactness, choice, or countable construction surface.
- `existence_mode`: none
- `cut_rank`: 0
- `equality_kind`: none
- `interpretation_kind`: none
- `resource_trace`: Consumes the displayed subject-reduction discharge interface and the finite BetaSubstitutionPreservation obligation row.
- `dependency_trace`: MetaCIC subject-reduction discharge interface; beta-redex substitution preservation obstruction; finite setup-obligation packaging.
- `oracle_mode`: failure_diagnosis
Rationale:
This is a BEDC-native proof-obligation target rather than a broad MetaCIC development: it records that the beta substitution case cannot be silently recovered from the parameterised subject-reduction theorem and must be exposed as a finite interface row. It is distinct from existing BOARD entries and lands as a small obligation block in proof_obligations, with a bounded resource surface.

---


### B-739 - MetaCIC appargtypestable discharge obligation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MetaCIC appargtypestable discharge obligation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_obligation |

Problem:
If the MetaCIC subject-reduction discharge interface is used, then the AppArgTypeStable row is an explicit finite setup obligation required by the interface.

Local inputs:
- `papers/bedc/parts/visions/metacic_open_problems.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: medium, the independent-codomain case is narrow but the dependent-codomain obstruction must not be overstated as solved

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The visible packet is a finite named congruence-stability setup row for one application-argument case.
- `existence_mode`: none
- `cut_rank`: 0
- `equality_kind`: none
- `interpretation_kind`: none
- `resource_trace`: Consumes the displayed subject-reduction discharge interface and the finite AppArgTypeStable obligation row.
- `dependency_trace`: MetaCIC subject-reduction discharge interface; application-argument congruence case; dependent-codomain readback stability obstruction.
- `oracle_mode`: failure_diagnosis
Rationale:
The target isolates a concrete finite proof obligation at the application-argument congruence boundary. It is not a marker or closure-status change and does not duplicate an existing BOARD theorem; it records a specific obstruction that must be present in the setup surface before subject reduction can be discharged.

---


### B-740 - MetaCIC lamdomainsubjectreduction discharge obligation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MetaCIC lamdomainsubjectreduction discharge obligation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_obligation |

Problem:
If the MetaCIC subject-reduction discharge interface is used, then the LamDomainSubjectReduction row is an explicit finite setup obligation required by the interface.

Local inputs:
- `papers/bedc/parts/visions/metacic_open_problems.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `ripeness_risk`: medium, the obligation is sharply stated but depends on keeping binder-domain preservation separate from nearby Pi-domain obligations

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The visible packet is a finite named setup row for one lambda-domain subject-reduction boundary case.
- `existence_mode`: none
- `cut_rank`: 0
- `equality_kind`: none
- `interpretation_kind`: none
- `resource_trace`: Consumes the displayed subject-reduction discharge interface and the finite LamDomainSubjectReduction obligation row.
- `dependency_trace`: MetaCIC subject-reduction discharge interface; lambda-domain congruence case; binder-annotation preservation obstruction.
- `oracle_mode`: failure_diagnosis
Rationale:
This candidate gives a small BEDC proof-obligation target for a concrete binder-domain preservation row. It is neither a general MetaCIC survey item nor a verification-axis marker; the downstream work should state the row as a required finite interface obligation and avoid claiming unconditional subject reduction.

---

