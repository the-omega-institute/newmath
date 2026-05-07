import BEDC.Derived.SheafUp
import BEDC.Derived.SheafUp.RootFaceReadback

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem SheafRootJointConsumerFace_normal_form_boundary {root endpoint : BHist} :
    SheafRootJointConsumerFace root endpoint ->
      ((∃ landing : SheafRootFaceLanding, SheafRootFaceRead root endpoint landing ∧
        ((landing = SheafRootFaceLanding.coverMembership ∧ hsame root endpoint) ∨
          (landing = SheafRootFaceLanding.restrictionRoute ∧
            (hsame root endpoint ∨ ∃ route : BHist, Cont root route endpoint)) ∨
          (landing = SheafRootFaceLanding.localityGluingRefinement ∧
            ∃ sectA : BHist, ∃ sectB : BHist, ∃ germB : BHist,
              Cont root sectA endpoint ∧ Cont root sectB germB ∧ hsame endpoint germB))) ∨
        ∃ common : BHist, ∃ sections : List BHist,
          SheafSchemeChartGluingTrace root common sections endpoint ∧ UnaryHistory endpoint) := by
  intro face
  cases face with
  | faceRead read =>
      exact Or.inl ⟨_, read, SheafRootFaceRead_normal_form_readback read⟩
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

theorem SheafRootJointConsumerFace_semantic_name_certificate {root endpoint : BHist} :
    SheafRootJointConsumerFace root endpoint ->
      SemanticNameCert (SheafRootJointConsumerFace root) (SheafRootJointConsumerFace root)
        (SheafRootJointConsumerFace root) hsame := by
  intro face
  constructor
  · constructor
    · exact Exists.intro endpoint face
    · intro candidate _carrier
      exact hsame_refl candidate
    · intro left right same
      exact hsame_symm same
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right same carrier
      cases same
      exact carrier
  · intro _candidate source
    exact source
  · intro _candidate source
    exact source

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

theorem SheafRootJointConsumerFace_chart_trace_e0_endpoint_absurd
    {root endpoint common tail : BHist} {sections : List BHist} :
    SheafSchemeChartGluingTrace root common sections endpoint ->
      hsame endpoint (BHist.e0 tail) -> False := by
  intro trace sameEndpoint
  exact unary_no_zero_extension
    (unary_transport (SheafSchemeChartGluingTrace_unary_result trace) sameEndpoint)

end BEDC.Derived.SheafUp
