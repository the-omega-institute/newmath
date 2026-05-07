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

theorem SheafRootJointConsumerFace_no_feedback_unary_boundary {root endpoint tail : BHist} :
    SheafRootJointConsumerFace root endpoint ->
      (forall landing : SheafRootFaceLanding,
        SheafRootFaceRead root endpoint landing -> False) ->
        hsame endpoint (BHist.e0 tail) -> False := by
  intro face noRootRead sameEndpoint
  cases face with
  | faceRead read =>
      exact noRootRead _ read
  | chartTrace trace =>
      exact unary_no_zero_extension
        (unary_transport (SheafSchemeChartGluingTrace_unary_result trace) sameEndpoint)

end BEDC.Derived.SheafUp
