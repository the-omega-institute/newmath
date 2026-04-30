import BEDC.FKernel.Gap.Core

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

variable [AskSetup] [PackageSetup] [G : DomainSetup]
theorem inGapSig_iff_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h ↔ InDom D h ∧ ∃ s : BHist, SigRel bundle h s ∧ TokIntro bundle s p := by
  rfl

theorem inGapSig_intro {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h s : BHist} :
    InDom D h -> SigRel bundle h s -> TokIntro bundle s p -> InGapSig bundle D p h := by
  intro hdom hsig htok
  exact And.intro hdom (Exists.intro s (And.intro hsig htok))

theorem inGapSig_domain_witness
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h -> InDom D h := by
  intro hgap
  exact hgap.left

theorem inGapSig_domain_transport_with_signature {bundle : ProbeBundle ProbeName}
    {D : Domain} {p : Pkg} {h k s : BHist} (policy : DomainPolicy D) :
    InGapSig bundle D p h -> hsame h k -> SigRel bundle k s ->
      TokIntro bundle s p -> InGapSig bundle D p k := by
  intro hgap hhk hsig htok
  have hdom : InDom D k := policy.transport (inGapSig_domain_witness hgap) hhk
  exact And.intro hdom (Exists.intro s (And.intro hsig htok))

theorem inGapSig_elim [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h ->
      InDom D h /\ exists s : BHist, SigRel bundle h s /\ TokIntro bundle s p := by
  intro hgap
  exact hgap

theorem inGapSig_domain_and_signature_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h ->
      InDom D h /\ exists s : BHist, SigRel bundle h s /\ TokIntro bundle s p := by
  intro hgap
  exact hgap

theorem inGapSig_domain_signature_token_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h ->
      InDom D h /\ exists s : BHist, SigRel bundle h s /\ TokIntro bundle s p := by
  intro hgap
  exact hgap

theorem inGapSig_witness_pair [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h ->
      exists s : BHist, InDom D h /\ SigRel bundle h s /\ TokIntro bundle s p := by
  intro hgap
  cases hgap with
  | intro hdom hsigTok =>
      cases hsigTok with
      | intro s hsigTokData =>
          cases hsigTokData with
          | intro hsig htok =>
              exact Exists.intro s (And.intro hdom (And.intro hsig htok))

theorem inGapSig_intro_from_witness_pair [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    (∃ s : BHist, InDom D h ∧ SigRel bundle h s ∧ TokIntro bundle s p) →
      InGapSig bundle D p h := by
  intro witness
  cases witness with
  | intro s data =>
      cases data with
      | intro hdom rest =>
          cases rest with
          | intro hsig htok =>
              exact And.intro hdom (Exists.intro s (And.intro hsig htok))

theorem inGapSig_signature_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h -> exists s : BHist, SigRel bundle h s /\ TokIntro bundle s p := by
  intro hgap
  exact hgap.right

theorem inGapSig_signature_and_token_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h -> exists s : BHist, SigRel bundle h s ∧ TokIntro bundle s p := by
  intro hgap
  exact hgap.right

theorem inGapSig_token_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h -> exists s : BHist, TokIntro bundle s p := by
  intro hgap
  cases hgap.right with
  | intro s data =>
      exact Exists.intro s data.right

theorem inGapSig_domain_token_witness [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h → InDom D h ∧ ∃ s : BHist, TokIntro bundle s p := by
  intro hgap
  constructor
  · exact hgap.left
  · cases hgap.right with
    | intro s data =>
        exact Exists.intro s data.right

theorem inGapSig_witnesses [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h : BHist} :
    InGapSig bundle D p h ->
      InDom D h /\ exists s : BHist, SigRel bundle h s /\ TokIntro bundle s p := by
  intro hgap
  exact hgap
end BEDC.FKernel.Gap
