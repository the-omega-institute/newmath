---
slug: cellstate-context-refresh-boundary
title: "Cell-state context refresh boundary as scoped NameCert promotion"
target_paper_section:
  - papers/cellstate_reality/parts/cellstate_context_refresh_boundary.tex
required_reality_contacts:
  - gse142439_epic_methylation_matrix
  - horvath_2013_353_cpg_clock_coefficients
  - paired_normal_treated_sample_rows
  - identity_retention_assay_for_age_reset_promotion
  - functional_repair_or_phenotype_assay_for_rejuvenation_promotion
  - repeat_cycle_time_horizon_for_renewable_maintenance
  - organismal_risk_survival_and_maintenance_contact_for_immortality_potential
required_gates:
  every_promotion_requires_recertification_at_its_scope: true
  age_clock_shift_is_the_first_publishable_name: true
  immortality_remains_blocked_null_without_organismal_horizon_contact: true
  no_cross_layer_claim_from_age_clock_rows_alone: true
forbidden_claims_to_check:
  - age_clock_shift_rephrased_as_identity_preserving_age_reset
  - dna_methylation_age_shift_rephrased_as_rejuvenation
  - partial_reprogramming_claim_without_state_boundary_contact
  - renewable_maintenance_claim_without_repeat_cycle_contact
  - immortality_or_immortality_potential_claim_without_organismal_horizon_contact
ripeness: ready
---

CellStateReality studies cell reprogramming, aging, and maintenance claims by
turning promotion into scoped re-certification. A local NameCert does not
become broader because its story is attractive. It becomes broader only when a
new carrier at the broader layer is assembled with its own reality contacts.

The working ladder is:

  DNA-as-source ->
  ContextDrift ->
  ContextRefresh ->
  IdentityPreservingAgeReset^up ->
  RejuvenationCandidate^up ->
  RenewableMaintenance_T ->
  ImmortalityPotential^up

Immortality^up remains blocked_null. The pipeline should treat that name as a
refusal boundary unless organismal maintenance, risk, repeated-cycle, and
survival-horizon contacts are present.

The first publishable object is AgeClockShift^up, not
IdentityPreservingAgeReset^up. The initial carrier is:

  B_A = (M, W, P, S_A, Delta_A, L, N)

where M is the GSE142439 EPIC methylation matrix row, W is the Horvath 2013
353-CpG clock coefficient row restricted to covered CpGs, P is the paired
normal/treated row, S_A is the computed age signature row, Delta_A is the
paired treated-minus-normal shift row, L is the no-promotion ledger, and N is
the local AgeClockShift^up NameCert row.

The reality contact is bounded:

  GSE142439 EPIC methylation matrix
  Horvath 2013 353-CpG clock coefficients
  8 paired normal/treated observations
  Horvath-intersection-EPIC coverage 334/353

Support condition:

  paired Delta_A < 0
  coverage >= 0.93 * 353
  paired rows are present

Break or suspension condition:

  paired Delta_A >= 0
  coverage < 0.93 * 353
  paired rows are absent

When support holds, the pipeline may write AgeClockShift^up. When support
fails, the local result becomes needs_data or broken at the age-clock layer.
Neither branch licenses a higher cell-state claim.

Thm3 clock-only no-promotion is the first theorem the paper should state:
given the age-layer contact above, a paired DNAm age-signature decrease permits
the local AgeClockShift^up name, while promotion to
IdentityPreservingAgeReset^up, RejuvenationCandidate^up,
PartialReprogramming^up, RenewableMaintenance_T, and
ImmortalityPotential^up remains blocked_null because B_A has no identity,
function, safety, repeat-cycle, or organismal maintenance row.

The cannot-claim ledger is part of the carrier:

  IdentityPreservingAgeReset^up is blocked without identity-retention contact.
  RejuvenationCandidate^up is blocked without function or repair contact.
  PartialReprogramming^up is blocked without reprogramming-state and identity
  boundary contact.
  RenewableMaintenance_T is blocked without repeated cycles over the time
  horizon T.
  ImmortalityPotential^up is blocked without organismal maintenance, risk, and
  survival-horizon contact.

The pipeline should prefer smaller publishable names over larger unsupported
names. AgeClockShift^up is valuable precisely because it is scoped, falsifiable,
and bounded by listed contacts. The next scientific work is not to rename that
contact as rejuvenation; it is to assemble the missing contacts for whichever
promotion target is actually being tested.
