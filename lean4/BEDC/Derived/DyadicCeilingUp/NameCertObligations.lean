import BEDC.Derived.DyadicCeilingUp.TasteGate

namespace BEDC.Derived.DyadicCeilingUp

open BEDC.Meta.TasteGate

theorem DyadicCeilingNameCertObligations :
    Nonempty (BHistCarrier DyadicCeilingUp) ∧
      Nonempty (ChapterTasteGate DyadicCeilingUp) ∧
        (∀ x : DyadicCeilingUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨dyadicCeilingBHistCarrier⟩
  · constructor
    · exact ⟨dyadicCeilingChapterTasteGate⟩
    · intro x
      exact ChapterTasteGate.round_trip x

end BEDC.Derived.DyadicCeilingUp
