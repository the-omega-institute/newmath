import BEDC.Derived.RegularCauchyTelescopingBudgetUp.TasteGate

namespace BEDC.Derived.RegularCauchyTelescopingBudgetUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem RegularCauchyTelescopingBudgetCarrier_visible_rows
    (x : RegularCauchyTelescopingBudgetUp) :
    ∃ E W D R S T H C P N : BHist,
      x = RegularCauchyTelescopingBudgetUp.mk E W D R S T H C P N ∧
        BHistCarrier.toEventFlow x = regularCauchyTelescopingBudgetToEventFlow x ∧
          hsame
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist E))
            E ∧
            hsame
              (regularCauchyTelescopingBudgetDecodeBHist
                (regularCauchyTelescopingBudgetEncodeBHist D))
              D := by
  -- BEDC touchpoint anchor: BHist BHistCarrier hsame
  cases x with
  | mk E W D R S T H C P N =>
      refine ⟨E, W, D, R, S, T, H, C, P, N, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · induction E with
        | Empty => rfl
        | e0 h ih => exact congrArg BHist.e0 ih
        | e1 h ih => exact congrArg BHist.e1 ih
      · induction D with
        | Empty => rfl
        | e0 h ih => exact congrArg BHist.e0 ih
        | e1 h ih => exact congrArg BHist.e1 ih

end BEDC.Derived.RegularCauchyTelescopingBudgetUp
