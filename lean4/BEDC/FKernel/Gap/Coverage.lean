import BEDC.FKernel.Gap.InGapSig

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

theorem gap_coverage_policy [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist} :
    AskPolicy (InDom D) -> (forall s : BHist, exists p : Pkg, TokIntro bundle s p) ->
      InDom D h -> exists p : Pkg, InGapSig bundle D p h := by
  intro policy tokenTotal hdom
  cases sig_total_from_policy (bundle := bundle) (D := InDom D) (h := h) policy hdom with
  | intro s hsig =>
      cases tokenTotal s with
      | intro p htok =>
          exact Exists.intro p
            (And.intro hdom
              (Exists.intro s
                (And.intro hsig htok)))

end BEDC.FKernel.Gap
