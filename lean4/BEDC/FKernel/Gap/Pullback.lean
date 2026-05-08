import BEDC.FKernel.Gap.Policy

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

def PulledBackInGapSig [AskSetup] [PackageSetup] [DomainSetup]
    (bundle : ProbeBundle ProbeName) (D' D : Domain) (pullback : BHist -> BHist)
    (p : Pkg) (h' : BHist) : Prop :=
  InDom D' h' ∧ InGapSig bundle D p (pullback h')

theorem PulledBackGapPolicy_coverage_separation [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D' D : Domain} {pullback : BHist -> BHist} :
    GapPolicy bundle D ->
      (forall {h' : BHist}, InDom D' h' -> InDom D (pullback h')) ->
        (forall {h' : BHist}, InDom D' h' ->
          exists p : Pkg, PulledBackInGapSig bundle D' D pullback p h') ∧
          (forall {h' : BHist} {p q : Pkg},
            PulledBackInGapSig bundle D' D pullback p h' ->
              PulledBackInGapSig bundle D' D pullback q h' -> psame bundle p q) := by
  intro policy sourcePreserves
  constructor
  · intro h' hdom'
    cases policy.coverage (sourcePreserves hdom') with
    | intro p hgap =>
        exact Exists.intro p (And.intro hdom' hgap)
  · intro h' p q hp hq
    exact policy.separation hp.right.left hp.right hq.right

end BEDC.FKernel.Gap
