import BEDC.Derived.ClosedNormalConfluenceSealUp.TasteGate
import BEDC.MetaCIC.Beta.Conversion

namespace BEDC.Derived.ClosedNormalConfluenceSealUp

open BEDC.FKernel.Hist
open BEDC.MetaCIC

theorem ClosedNormalConfluenceSealNormalSource
    {source normal routeLeft routeRight join transports continuations provenance nameCert :
      BHist}
    {t u v : Term}
    (normalSource : BetaStrong t)
    (leftRoute : BetaStarStep t u)
    (rightRoute : BetaStarStep t v) :
    (∃ w : Term, BetaStarStep u w ∧ BetaStarStep v w) ∧
      closedNormalConfluenceSealToEventFlow
          (ClosedNormalConfluenceSealUp.mk source normal routeLeft routeRight join
            transports continuations provenance nameCert) ≠
        [] := by
  -- BEDC touchpoint anchor: BHist BetaStrong BetaStarStep ClosedNormalConfluenceSealUp
  have betaNormal : BetaNormal t := betaNormal_of_betaStrong normalSource
  have leftBack : BetaStarStep u t :=
    betaStarStep_of_normal_source betaNormal leftRoute
  have rightBack : BetaStarStep v t :=
    betaStarStep_of_normal_source betaNormal rightRoute
  constructor
  · exact ⟨t, leftBack, rightBack⟩
  · intro h
    cases h

end BEDC.Derived.ClosedNormalConfluenceSealUp
