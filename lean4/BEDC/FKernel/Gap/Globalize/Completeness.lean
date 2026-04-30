import BEDC.FKernel.Gap.Globalize

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

theorem concrete_globalization_completeness_samesig [AskSetup] [PackageSetup] [DomainSetup]
    {bundle : ProbeBundle ProbeName} {D : Domain} {h k : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> InGapSig bundle D p h -> InGapSig bundle D q k ->
      psame bundle p q -> SameSig bundle h k := by
  intro packagePolicy hp hq hpq
  unfold InGapSig at hp
  unfold InGapSig at hq
  cases hp with
  | intro _ hpSig =>
      cases hq with
      | intro _ hqSig =>
          cases hpSig with
          | intro s hsData =>
              cases hqSig with
              | intro t htData =>
                  cases hsData with
                  | intro hs hpTok =>
                      cases htData with
                      | intro ht hqTok =>
                          exact Exists.intro s
                            (Exists.intro t
                              (And.intro hs
                                (And.intro ht
                                  (packagePolicy.reflection hpTok hqTok hpq))))

end BEDC.FKernel.Gap
