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

### B-733 - RegularCauchyTailSchedule seal-facing route determinacy

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | RegularCauchyTailSchedule seal-facing route determinacy |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If two accepted RegularCauchyTailScheduleUp packets share the precision request, RegSeqRat source, StreamName window schedule, DyadicRatCore ledger, cofinal index, tail witness, sibling consumer rows, transport, continuation, provenance, and naming rows, then their RealUp seal-facing handoff rows are hsame.

Local inputs:
- `papers/bedc/parts/concrete_instances/4689_regularcauchytailschedule_namecert_construction.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The schedule is a displayed finite packet; the handoff comparison is a finite route-readback argument through named rows Q,R,W,D,K,T,M,F,H,C,P,N.
- `witness_extractor`: regular_cauchy_tail_schedule_handoff_route
- `existence_mode`: constructive_witness
- `cut_rank`: 1
- `elimination_plan`: Cut through the cofinal-index/tail-witness pair K,T: align the shared precision, window, dyadic, and sibling consumer rows, then use C and H to compare the two E handoff endpoints.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: none
- `resource_trace`: Consumes Q,R,W,D,K,T,M,F,E,H,C,P,N from the carrier; the sibling TailMeet and TailFusion rows are read only as displayed consumer rows, with no quotient stream equality, selected limit, or ambient completeness principle.
- `dependency_trace`: Builds on papers/bedc/parts/concrete_instances/4689_regularcauchytailschedule_namecert_construction.tex:7 for the carrier and papers/bedc/parts/concrete_instances/4689_regularcauchytailschedule_namecert_construction.tex:32 for the local obligation rows.
- `rate_modulus_surface`: Finite precision request Q, finite window schedule W, DyadicRatCore tolerance ledger D, and cofinal index K form the complete modulus surface.
- `oracle_mode`: proof_search
Rationale:
The carrier at papers/bedc/parts/concrete_instances/4689_regularcauchytailschedule_namecert_construction.tex:7 is a finite BHist packet S=(Q,R,W,D,K,T,M,F,E,H,C,P,N); lines 15-23 describe the precision request, window schedule, dyadic ledger, cofinal index, tail witness, sibling consumer rows, and seal-facing handoff. The existing theorem at lines 32-42 gives NameCert obligation rows but does not state a two-packet handoff determinacy result. Focused grep for RegularCauchyTailSchedule and schedule/tail determinacy returned only this file's carrier and obligation labels plus neighboring general tail-meet or diagonal-tail theorems, so this packet-specific claim remains open and is not merely a parameter transport echo.

---


### B-734 - InducedRep restriction-induction classifier equivalence

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InducedRep restriction-induction classifier equivalence |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |
| Landing kind | existing_chapter_lemma |

Problem:
If the consumed SubgroupUp and RepresentationRingUp classifiers, endpoint hsame rows, Frobenius hsame rows, provenance hsame row, and continuation-ledger comparisons are equivalence-stable, then the InducedRepUp restriction-induction classifier is reflexive, symmetric, and transitive on accepted carrier packets.

Local inputs:
- `papers/bedc/parts/concrete_instances/inducedrep/carrier_definition.tex`
- `papers/bedc/parts/concrete_instances/inducedrep/stability_and_consumption.tex`


Logic packet discipline:
- `axiom_budget`: B0_finite_witness
- `strength_level`: B0_finite_witness
- `budget_reason`: The classifier is a finite componentwise tuple; equivalence closure is obtained by projecting and repacking finitely many hsame and Cont comparison rows.
- `witness_extractor`: inducedrep_componentwise_classifier_tuple
- `existence_mode`: constructive_witness
- `cut_rank`: 0
- `elimination_plan`: No bridge cut is needed; prove reflexivity, symmetry, and transitivity by componentwise projection over S,R,i,r,F,eta,epsilon,rho,lambda and repack the classifier tuple.
- `equality_kind`: propositionally_equal
- `interpretation_kind`: none
- `resource_trace`: Consumes the finite carrier packet S,R,i,r,F,eta,epsilon,rho,lambda and the classifier tuple rows for source certificates, endpoints, Frobenius rows, provenance, and Cont ledger comparison.
- `dependency_trace`: Builds on the carrier definition in papers/bedc/parts/concrete_instances/inducedrep/carrier_definition.tex:4, the restriction-induction classifier definition at papers/bedc/parts/concrete_instances/inducedrep/carrier_definition.tex:59, and the stability obligation packet in papers/bedc/parts/concrete_instances/inducedrep/stability_and_consumption.tex:31.
- `oracle_mode`: proof_search
Rationale:
The restriction-induction classifier is defined concretely at papers/bedc/parts/concrete_instances/inducedrep/carrier_definition.tex:59 as seven componentwise transport fields, and the stability obligation packet at papers/bedc/parts/concrete_instances/inducedrep/stability_and_consumption.tex:31 repacks those fields. The existing classifier-stability theorem at lines 60-70 transports carrier components, but a focused grep for inducedrep/restriction-induction classifier reflexive, symmetric, transitive, or equivalence returned 0 hits in the inducedrep chapter. This is a genuine certificate-level gap: the NameCert surface relies on classifier equivalence, yet the paper has stability and boundary theorems without a standalone classifier-equivalence package.

---

