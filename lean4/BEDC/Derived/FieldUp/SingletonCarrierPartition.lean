import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem FieldSingletonCarrier_empty_or_visible_absurd {h : BHist} :
    (h = BHist.Empty ∧ FieldSingletonCarrier h) ∨
      (∃ p : BHist, h = BHist.e0 p ∧ (FieldSingletonCarrier h -> False)) ∨
        (∃ p : BHist, h = BHist.e1 p ∧ (FieldSingletonCarrier h -> False)) := by
  cases h with
  | Empty =>
      left
      constructor
      · rfl
      · exact hsame_refl BHist.Empty
  | e0 p =>
      right
      left
      exact ⟨p, rfl, fun carrier => not_hsame_e0_empty carrier⟩
  | e1 p =>
      right
      right
      exact ⟨p, rfl, fun carrier => not_hsame_e1_empty carrier⟩

end BEDC.Derived.FieldUp
