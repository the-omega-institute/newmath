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
omit [AskSetup] [PackageSetup] in
theorem domain_transport {D : Domain} (policy : DomainPolicy D) {h k : BHist} :
    InDom D h → hsame h k → InDom D k := by
  intro hh hhk
  exact policy.transport hh hhk

theorem domain_transport_refl [AskSetup] [PackageSetup] [DomainSetup] {D : Domain}
    (policy : DomainPolicy D) {h : BHist} :
    InDom D h -> InDom D h := by
  intro hdom
  exact policy.transport hdom (hsame_refl h)

theorem DomainPolicy_iff_transport [AskSetup] [PackageSetup] [DomainSetup] {D : Domain} :
    DomainPolicy D <-> (forall {h k : BHist}, InDom D h -> hsame h k -> InDom D k) := by
  constructor
  case mp =>
    intro policy
    exact policy.transport
  case mpr =>
    intro transport
    exact {
      transport := transport
    }

theorem inGapSig_domain_transport_source [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {p : Pkg} {h k : BHist}
    (policy : DomainPolicy D) :
    InGapSig bundle D p h -> hsame h k -> InDom D k := by
  intro hgap hhk
  exact policy.transport hgap.left hhk

theorem domain_transport_symmetric [AskSetup] [PackageSetup] [DomainSetup]
    {D : Domain} (policy : DomainPolicy D) {h k : BHist} :
    InDom D k → hsame h k → InDom D h := by
  intro hk hhk
  exact policy.transport hk (hsame_symm hhk)

omit [AskSetup] [PackageSetup] in
theorem domain_invariance {D : Domain} (policy : DomainPolicy D) {h k : BHist} :
    hsame h k -> (InDom D h <-> InDom D k) := by
  intro hhk
  constructor
  · intro hh
    exact policy.transport hh hhk
  · intro hk
    exact policy.transport hk (hsame_symm hhk)
end BEDC.FKernel.Gap
