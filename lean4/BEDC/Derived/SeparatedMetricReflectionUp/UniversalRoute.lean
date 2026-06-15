import BEDC.Derived.SeparatedMetricReflectionUp.TasteGate

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem SeparatedMetricReflectionCarrier_universal_route :
    Nonempty (ChapterTasteGate SeparatedMetricReflectionUp) ∧
      (∀ x : SeparatedMetricReflectionUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        (∀ x : SeparatedMetricReflectionUp,
          ∃ X S A U Z H C P N : BHist,
            x = SeparatedMetricReflectionUp.mk X S A U Z H C P N ∧
              FieldFaithful.fields x = [X, S, A, U, Z, H, C, P, N]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨separatedMetricReflectionChapterTasteGate⟩,
      by
        intro x
        exact ChapterTasteGate.round_trip x,
      by
        intro x
        cases x with
        | mk X S A U Z H C P N =>
            exact ⟨X, S, A, U, Z, H, C, P, N, rfl, rfl⟩⟩

end BEDC.Derived.SeparatedMetricReflectionUp
