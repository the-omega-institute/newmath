import BEDC.Derived.GroundCompilerRecognitionUp.TasteGate

namespace BEDC.Derived.GroundCompilerRecognitionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem GroundCompilerRecognitionReportBoundary_exhaustion :
    (∀ x : GroundCompilerRecognitionUp,
      ∃ I G A T V L H C P N : BHist,
        x = GroundCompilerRecognitionUp.mk I G A T V L H C P N ∧
          FieldFaithful.fields x = [I, G, A, T, V, L, H, C, P, N]) ∧
      (∀ I G A T L H C P N : BHist,
        FieldFaithful.fields
            (GroundCompilerRecognitionUp.mk I G A T (BHist.e0 BHist.Empty) L H C P N) ≠
          FieldFaithful.fields
            (GroundCompilerRecognitionUp.mk I G A T BHist.Empty L H C P N)) ∧
        (∀ _I _G _A _T _V _L H C P _N : BHist, hsame H H ∧ Cont C P (append C P)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk I G A T V L H C P N =>
        exact ⟨I, G, A, T, V, L, H, C, P, N, rfl, rfl⟩
  · constructor
    · intro I G A T L H C P N hfields
      cases hfields
    · intro _ _ _ _ _ _ H C P _
      exact ⟨hsame_refl H, rfl⟩

end BEDC.Derived.GroundCompilerRecognitionUp
