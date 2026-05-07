import BEDC.Derived.SheafUp

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

end BEDC.Derived.SheafUp
