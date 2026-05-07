import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem SheafRootFaceRead_restriction_route_readback {h k : BHist} :
    SheafRootFaceRead h k SheafRootFaceLanding.restrictionRoute ->
      hsame h k ∨ ∃ sectionHist : BHist, Cont h sectionHist k := by
  intro read
  cases read with
  | carrierClassifier same =>
      exact Or.inl same
  | restrictionRoute route =>
      exact Or.inr (Exists.intro _ route)

end BEDC.Derived.SheafUp
