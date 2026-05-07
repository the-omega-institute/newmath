import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive SheafRootJointConsumerFace (root endpoint : BHist) : Prop where
  | faceRead {landing : SheafRootFaceLanding} :
      SheafRootFaceRead root endpoint landing -> SheafRootJointConsumerFace root endpoint
  | chartTrace {common : BHist} {sections : List BHist} :
      SheafSchemeChartGluingTrace root common sections endpoint ->
        SheafRootJointConsumerFace root endpoint

theorem SheafRootJointConsumerFace_exhaustion {root endpoint : BHist} :
    SheafRootJointConsumerFace root endpoint ->
      (∃ landing : SheafRootFaceLanding, SheafRootFaceRead root endpoint landing ∧
        (landing = SheafRootFaceLanding.coverMembership ∨
          landing = SheafRootFaceLanding.restrictionRoute ∨
            landing = SheafRootFaceLanding.localityGluingRefinement)) ∨
      (∃ common : BHist, ∃ sections : List BHist,
        SheafSchemeChartGluingTrace root common sections endpoint ∧ UnaryHistory endpoint) := by
  intro face
  cases face with
  | faceRead read =>
      exact Or.inl ⟨_, read, SheafRootFaceRead_coverage read⟩
  | chartTrace trace =>
      exact Or.inr ⟨_, _, trace, SheafSchemeChartGluingTrace_unary_result trace⟩

theorem SheafRootJointConsumerFace_noninterference {root endpoint : BHist} :
    SheafRootJointConsumerFace root endpoint ->
      (∀ privateEndpoint : BHist,
        hsame privateEndpoint (BHist.e0 endpoint) -> UnaryHistory privateEndpoint -> False) ∧
        ((∃ landing : SheafRootFaceLanding, SheafRootFaceRead root endpoint landing) ∨
          (∃ common : BHist, ∃ sections : List BHist,
            SheafSchemeChartGluingTrace root common sections endpoint)) := by
  intro face
  constructor
  · intro privateEndpoint samePrivate privateUnary
    exact unary_no_zero_extension (unary_transport privateUnary samePrivate)
  · cases face with
    | faceRead read =>
        exact Or.inl ⟨_, read⟩
    | chartTrace trace =>
        exact Or.inr ⟨_, _, trace⟩

end BEDC.Derived.SheafUp
