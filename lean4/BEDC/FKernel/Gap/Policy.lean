import BEDC.FKernel.Gap.InGapSig

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

variable [AskSetup] [PackageSetup] [G : DomainSetup]
structure GapPolicy (bundle : ProbeBundle ProbeName) (D : Domain) : Prop where
  generation : ∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h → ∃ s : BHist, TokIntro bundle s p
  coverage : ∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h
  separation : ∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q

def GapPolicyInterface [AskSetup] [PackageSetup] [DomainSetup]
    (bundle : ProbeBundle ProbeName) (D : Domain) : Prop :=
  GapPolicy bundle D

theorem gap_policy_fields {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      (∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h →
        InGapSig bundle D q h → psame bundle p q) ∧
      (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h → ∃ s : BHist, TokIntro bundle s p) := by
  constructor
  · exact policy.coverage
  · constructor
    · exact policy.separation
    · exact policy.generation

theorem compression_requires_memory [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} :
    GapPolicy bundle D ->
      (forall {h : BHist}, InDom D h -> exists p : Pkg, InGapSig bundle D p h) ∧
        (forall {p : Pkg} {h : BHist}, InGapSig bundle D p h ->
          exists s : BHist, TokIntro bundle s p) := by
  intro policy
  constructor
  · exact policy.coverage
  · exact policy.generation

theorem gapPolicy_provenance_interface_fields [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      (∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h →
        InGapSig bundle D q h → psame bundle p q) ∧
      (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h →
        ∃ s : BHist, TokIntro bundle s p) := by
  exact gap_policy_fields policy

theorem gapPolicy_provenance_coverage_generation_pair [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h →
        ∃ s : BHist, SigRel bundle h s ∧ TokIntro bundle s p) := by
  constructor
  · intro h hdom
    exact policy.coverage hdom
  · intro p h hgap
    exact hgap.right

theorem gapPolicy_coverage_separation_generation [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      (∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h →
        InGapSig bundle D q h → psame bundle p q) ∧
      (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h →
        ∃ s : BHist, SigRel bundle h s ∧ TokIntro bundle s p) := by
  constructor
  · exact policy.coverage
  · constructor
    · exact policy.separation
    · intro p h hgap
      exact hgap.right

theorem gap_policy_provenance_interface [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      (∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h →
        InGapSig bundle D q h → psame bundle p q) ∧
      (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h →
        ∃ s : BHist, SigRel bundle h s ∧ TokIntro bundle s p) := by
  exact gapPolicy_coverage_separation_generation policy

theorem GapPolicy_iff_fields [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} :
    GapPolicy bundle D <->
      ((forall {h : BHist}, InDom D h -> exists p : Pkg, InGapSig bundle D p h) /\
        (forall {h : BHist} {p q : Pkg}, InDom D h -> InGapSig bundle D p h ->
          InGapSig bundle D q h -> psame bundle p q) /\
        (forall {p : Pkg} {h : BHist}, InGapSig bundle D p h ->
          exists s : BHist, TokIntro bundle s p)) := by
  constructor
  case mp =>
    intro policy
    exact gap_policy_fields policy
  case mpr =>
    intro fields
    cases fields with
    | intro coverage rest =>
        cases rest with
        | intro separation generation =>
            exact {
              generation := generation
              coverage := coverage
              separation := separation
            }

omit [AskSetup] [PackageSetup] G in
theorem GapPolicyInterface_iff_fields [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} :
    GapPolicyInterface bundle D ↔
      ((∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
        (∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h →
          InGapSig bundle D q h → psame bundle p q) ∧
        (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h →
          ∃ s : BHist, TokIntro bundle s p)) := by
  exact GapPolicy_iff_fields

theorem globalization_has_three_layers [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} :
    AskPolicy (InDom D) → PackagePolicy bundle → GapPolicy bundle D →
      AskPolicy (InDom D) ∧ PackagePolicy bundle ∧ GapPolicy bundle D := by
  intro askPolicy packagePolicy gapPolicy
  constructor
  · exact askPolicy
  · constructor
    · exact packagePolicy
    · exact gapPolicy

theorem gap_coverage_from_policy_layers [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} :
    AskPolicy (InDom D) -> PackagePolicy bundle -> GapPolicy bundle D -> InDom D h ->
      exists p : Pkg, InGapSig bundle D p h := by
  intro _ _ gapPolicy hdom
  exact gapPolicy.coverage hdom

theorem gap_generation_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist}
    (policy : GapPolicy bundle D) :
    InGapSig bundle D p h → ∃ s : BHist, TokIntro bundle s p := by
  intro hgap
  exact policy.generation hgap

theorem gapPolicy_generation_field [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {p : Pkg} {h : BHist}, InGapSig bundle D p h →
      ∃ s : BHist, TokIntro bundle s p) := by
  exact policy.generation

theorem gapPolicy_separation_field [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) :
    (∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig bundle D p h →
      InGapSig bundle D q h → psame bundle p q) := by
  exact policy.separation

theorem gapPolicy_separation_packed [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg} :
    GapPolicy bundle D → InDom D h → InGapSig bundle D p h ∧ InGapSig bundle D q h →
      psame bundle p q := by
  intro policy hdom hgap
  exact policy.separation hdom hgap.left hgap.right

theorem policy_gap_separation_signature_token_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg}
    (policy : GapPolicy bundle D) :
    InDom D h → InGapSig bundle D p h → InGapSig bundle D q h →
      psame bundle p q ∧ ∃ s : BHist, ∃ t : BHist,
        SigRel bundle h s ∧ TokIntro bundle s p ∧
          SigRel bundle h t ∧ TokIntro bundle t q := by
  intro hdom hp hq
  constructor
  · exact policy.separation hdom hp hq
  · cases hp.right with
    | intro s psigTok =>
        cases psigTok with
        | intro psig ptok =>
            cases hq.right with
            | intro t qsigTok =>
                cases qsigTok with
                | intro qsig qtok =>
                    exact Exists.intro s
                      (Exists.intro t
                        (And.intro psig (And.intro ptok (And.intro qsig qtok))))

theorem gapPolicy_signature_determination [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist}
    (_policy : GapPolicy bundle D) :
    InGapSig bundle D p h → ∃ s : BHist, SigRel bundle h s ∧ TokIntro bundle s p := by
  intro hgap
  exact hgap.right

theorem gapPolicy_requires_ledger_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) {h : BHist} :
    InDom D h -> ∃ p : Pkg, ∃ s : BHist, InGapSig bundle D p h ∧ TokIntro bundle s p := by
  intro hdom
  cases policy.coverage hdom with
  | intro p hgap =>
      cases policy.generation hgap with
      | intro s htok =>
          exact Exists.intro p (Exists.intro s (And.intro hgap htok))

theorem gap_ledgers_not_optional [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) {h : BHist} :
    InDom D h → ∃ p : Pkg, ∃ s : BHist, InGapSig bundle D p h ∧ TokIntro bundle s p := by
  intro hdom
  cases policy.coverage hdom with
  | intro p hgap =>
      cases policy.generation hgap with
      | intro s htok =>
          exact Exists.intro p (Exists.intro s (And.intro hgap htok))

theorem gapPolicy_requires_provenance_ledger [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) {h : BHist} :
    InDom D h -> exists p : Pkg, exists s : BHist, InGapSig bundle D p h /\ TokIntro bundle s p := by
  intro hdom
  cases policy.coverage hdom with
  | intro p hgap =>
      cases policy.generation hgap with
      | intro s htok =>
          exact Exists.intro p (Exists.intro s (And.intro hgap htok))

theorem gapPolicy_coverage_signature_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) {h : BHist} :
    InDom D h -> exists p : Pkg, exists s : BHist,
      InGapSig bundle D p h /\ SigRel bundle h s /\ TokIntro bundle s p := by
  intro hdom
  cases policy.coverage hdom with
  | intro p hgap =>
      cases hgap.right with
      | intro s hsigTok =>
          cases hsigTok with
          | intro hsig htok =>
              exact Exists.intro p
                (Exists.intro s (And.intro hgap (And.intro hsig htok)))

theorem gapPolicy_coverage_full_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D) {h : BHist} :
    InDom D h → ∃ p : Pkg, ∃ s : BHist,
      InGapSig bundle D p h ∧ InDom D h ∧ SigRel bundle h s ∧ TokIntro bundle s p := by
  intro hdom
  cases policy.coverage hdom with
  | intro p hgap =>
      cases hgap.right with
      | intro s hsigTok =>
          cases hsigTok with
          | intro hsig htok =>
              exact Exists.intro p
                (Exists.intro s (And.intro hgap (And.intro hdom (And.intro hsig htok))))

theorem gapPolicy_provenance_signature_token_witnesses [AskSetup] [PackageSetup]
    [DomainSetup] {bundle : ProbeBundle ProbeName} {D : Domain} (policy : GapPolicy bundle D)
    {h : BHist} :
    InDom D h → ∃ p : Pkg, ∃ s : BHist,
      InGapSig bundle D p h ∧ SigRel bundle h s ∧ TokIntro bundle s p := by
  intro hdom
  cases policy.coverage hdom with
  | intro p hgap =>
      cases hgap.right with
      | intro s data =>
          cases data with
          | intro hsig htok =>
              exact Exists.intro p (Exists.intro s (And.intro hgap (And.intro hsig htok)))

theorem gap_coverage :
    ∀ {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist},
      GapPolicy bundle D → InDom D h → ∃ p : Pkg, InGapSig bundle D p h := by
  intro bundle D h hgap hh
  exact hgap.coverage hh

theorem gap_separation :
    ∀ {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} {p q : Pkg},
      GapPolicy bundle D → InDom D h → InGapSig bundle D p h → InGapSig bundle D q h → psame bundle p q := by
  intro bundle D h p q hgap hh hp hq
  exact hgap.separation hh hp hq
end BEDC.FKernel.Gap
