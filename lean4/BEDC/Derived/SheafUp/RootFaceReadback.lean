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

theorem SheafRootFaceRead_locality_gluing_readback {h k : BHist} :
    SheafRootFaceRead h k SheafRootFaceLanding.localityGluingRefinement ->
      exists sectA : BHist, exists sectB : BHist, exists germB : BHist,
        Cont h sectA k ∧ Cont h sectB germB ∧ hsame k germB := by
  intro read
  cases read with
  | localityGluingRefinement rowA rowB same =>
      exact Exists.intro _
        (Exists.intro _
          (Exists.intro _
            (And.intro rowA
              (And.intro rowB same))))

end BEDC.Derived.SheafUp
