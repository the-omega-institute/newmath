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

theorem SheafRootAccessNormalForm_no_extra_rows
    {h k : BHist} {landing : SheafRootFaceLanding} :
    SheafRootFaceRead h k landing ->
      (landing = .coverMembership -> hsame h k) ∧
        (landing = .restrictionRoute -> hsame h k ∨ ∃ sectionHist : BHist, Cont h sectionHist k) ∧
          (landing = .localityGluingRefinement ->
            ∃ sectA : BHist, ∃ sectB : BHist, ∃ germB : BHist,
              Cont h sectA k ∧ Cont h sectB germB ∧ hsame k germB) := by
  intro read
  constructor
  · intro cover
    cases cover
    cases read with
    | coverMembership same =>
        exact same
  · constructor
    · intro restriction
      cases restriction
      exact SheafRootFaceRead_restriction_route_readback read
    · intro locality
      cases locality
      exact SheafRootFaceRead_locality_gluing_readback read

theorem SheafRootFaceRead_normal_form_readback
    {root endpoint : BHist} {landing : SheafRootFaceLanding} :
    SheafRootFaceRead root endpoint landing ->
      (landing = SheafRootFaceLanding.coverMembership ∧ hsame root endpoint) ∨
        (landing = SheafRootFaceLanding.restrictionRoute ∧
          (hsame root endpoint ∨ ∃ route : BHist, Cont root route endpoint)) ∨
          (landing = SheafRootFaceLanding.localityGluingRefinement ∧
            ∃ sectA : BHist, ∃ sectB : BHist, ∃ germB : BHist,
              Cont root sectA endpoint ∧ Cont root sectB germB ∧ hsame endpoint germB) := by
  intro read
  cases read with
  | carrierClassifier same =>
      exact Or.inr (Or.inl (And.intro rfl (Or.inl same)))
  | restrictionRoute route =>
      exact Or.inr (Or.inl (And.intro rfl (Or.inr (Exists.intro _ route))))
  | coverMembership same =>
      exact Or.inl (And.intro rfl same)
  | localityGluingRefinement rowA rowB same =>
      exact Or.inr (Or.inr (And.intro rfl
        (Exists.intro _
          (Exists.intro _
            (Exists.intro _
              (And.intro rowA
                (And.intro rowB same)))))))

end BEDC.Derived.SheafUp
