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

### B-748 - MetaCIC pidomainsubjectreduction discharge obligation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | MetaCIC pidomainsubjectreduction discharge obligation |
| Layer | proof_obligations |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_obligation |

Problem:
If a MetaCIC subject-reduction consumer uses either the explicit discharge bundle route or the setup route for the Pi-domain congruence branch, then the finite discharge packet must contain a distinct row satisfying PiDomainSubjectReduction, and that row cannot be supplied by the beta, application-argument, lambda-domain, transport, route-replay, provenance, or naming coordinates.

Local inputs:
- `papers/bedc/parts/visions/metacic_open_problems.tex`


Pre-TasteGate admission:
- `tastegate_mode`: existing_chapter
- `elimination_plan`: cut_rank 0: prove by direct projection from the four-row SubjectReductionDischargeBundle or SubjectReductionSetup-to-bundle surface and the existing finite discharge socket/ledger rows, with no intermediate bridge or transported theorem.
- `ripeness_risk`: low, because the paper already contains the three sibling mandatory-row propositions and the Pi-domain row is named in the same four-obligation interface.

Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The claim only requires reading a finite four-field discharge packet and separating one displayed row from the other displayed rows.
- `witness_extractor`: projection of the Pi-domain coordinate from the finite discharge bundle, setup-converted bundle, socket, or ledger carrier.
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `elimination_plan`: cut_rank 0: prove by direct projection from the four-row SubjectReductionDischargeBundle or SubjectReductionSetup-to-bundle surface and the existing finite discharge socket/ledger rows, with no intermediate bridge or transported theorem.
- `equality_kind`: none
- `interpretation_kind`: none
- `resource_trace`: finite discharge rows B,A,L,P plus route/support rows from the subject-reduction discharge interface.
- `dependency_trace`: def:metacic-pi-domain-subject-reduction; sec:metacic-subject-reduction-four-obligations; SubjectReductionDischargeBundle; SubjectReductionSetup; def:subject-reduction-discharge-ledger-carrier; subject-reduction discharge socket/ledger four-row exposure.
- `oracle_mode`: rewrite_to_packet
Rationale:
This is the missing fourth sibling of the already completed beta-substitution, application-argument, and lambda-domain mandatory discharge-row targets. It is concrete, BEDC-native, and lands as an existing-chapter obligation rather than a new chapter. It is not merely a verification marker or closurestatus item: the downstream work is a proposition/obligation block showing that the Pi-domain row remains an explicit finite setup input whenever the subject-reduction discharge interface is consumed.

---

