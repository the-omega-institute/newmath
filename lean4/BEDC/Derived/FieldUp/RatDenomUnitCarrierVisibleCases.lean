import BEDC.Derived.FieldUp.RatDenomUnitEndpointAbsurd

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatDenomUnitCarrier_visible_cases {h : BHist} :
    RatDenomUnitCarrier h ->
      hsame h BHist.Empty ∨ Exists (fun tail : BHist => h = BHist.e1 tail ∧ UnaryHistory tail) := by
  intro carrier
  cases h with
  | Empty =>
      left
      exact hsame_refl BHist.Empty
  | e0 tail =>
      exact False.elim (RatDenomUnitCarrier_e0_absurd carrier)
  | e1 tail =>
      right
      exact Exists.intro tail (And.intro rfl (RatDenomUnitCarrier_e1_tail_unary_iff.mp carrier))

end BEDC.Derived.FieldUp
