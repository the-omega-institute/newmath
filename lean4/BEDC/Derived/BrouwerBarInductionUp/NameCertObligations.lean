import BEDC.Derived.BrouwerBarInductionUp.TasteGate

namespace BEDC.Derived.BrouwerBarInductionUp

open BEDC.Meta.TasteGate

theorem BrouwerBarInductionNameCertObligations :
    Nonempty (BHistCarrier BrouwerBarInductionUp) ∧
      Nonempty (ChapterTasteGate BrouwerBarInductionUp) ∧
        (∀ x : BrouwerBarInductionUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨brouwerBarInductionBHistCarrier⟩
  · constructor
    · exact ⟨brouwerBarInductionChapterTasteGate⟩
    · intro x
      exact ChapterTasteGate.round_trip x

end BEDC.Derived.BrouwerBarInductionUp
