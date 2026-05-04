import BEDC.Derived.RatUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem PositiveUnaryDenominator_append_factor_or_tail {d tail : BHist} :
    PositiveUnaryDenominator (BEDC.FKernel.Cont.append d tail) ->
      PositiveUnaryDenominator d ∨ PositiveUnaryDenominator tail := by
  intro positive
  cases tail with
  | Empty =>
      exact Or.inl positive
  | e0 tail =>
      exact False.elim (PositiveUnaryDenominator_e0_absurd positive)
  | e1 tail =>
      have appendUnary : UnaryHistory (append d tail) :=
        PositiveUnaryDenominator_e1_iff_unary.mp positive
      exact Or.inr
        (PositiveUnaryDenominator_e1_iff_unary.mpr
          (unary_append_right_factor appendUnary))

end BEDC.Derived.RatUp
