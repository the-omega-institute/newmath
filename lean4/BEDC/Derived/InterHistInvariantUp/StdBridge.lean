import BEDC.Derived.InterHistInvariantUp.TasteGate

namespace BEDC.Derived.InterHistInvariantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem InterHistInvariantUp_StdBridge :
    (∃ x y : InterHistInvariantUp, x ≠ y) ∧
      Nonempty (FieldFaithful InterHistInvariantUp) ∧
        Nonempty (ChapterTasteGate InterHistInvariantUp) ∧
          (∀ h : BHist, interHistInvariantDecodeBHist (interHistInvariantEncodeBHist h) = h) ∧
            interHistInvariantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact
      ⟨InterHistInvariantUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        InterHistInvariantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩
  · constructor
    · exact ⟨InterHistInvariantUp_StdBridge_field_faithful⟩
    · constructor
      · exact ⟨interHistInvariantChapterTasteGate⟩
      · constructor
        · intro h
          induction h with
          | Empty =>
              rfl
          | e0 h ih =>
              exact congrArg BHist.e0 ih
          | e1 h ih =>
              exact congrArg BHist.e1 ih
        · rfl

end BEDC.Derived.InterHistInvariantUp
