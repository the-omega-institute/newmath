import BEDC.Derived.RatUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_positive_denominator_append_split {h k : BHist} :
    PositiveUnaryDenominator (append h k) ->
      PositiveUnaryDenominator h ∨ PositiveUnaryDenominator k := by
  intro positive
  cases k with
  | Empty =>
      exact Or.inl positive
  | e0 tail =>
      exact False.elim (PositiveUnaryDenominator_e0_absurd positive)
  | e1 tail =>
      have appendUnary : UnaryHistory (append h tail) :=
        PositiveUnaryDenominator_e1_iff_unary.mp positive
      exact Or.inr
        (PositiveUnaryDenominator_e1_iff_unary.mpr
          (unary_append_right_factor appendUnary))

end BEDC.Derived.FieldUp
