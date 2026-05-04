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

theorem PositiveUnaryDenominator_append_e1_left_iff {head tail : BHist} :
    PositiveUnaryDenominator (BEDC.FKernel.Cont.append (BHist.e1 head) tail) ↔
      UnaryHistory head ∧ UnaryHistory tail := by
  constructor
  · intro positive
    have appendUnary : UnaryHistory (append (BHist.e1 head) tail) :=
      (PositiveUnaryDenominator_unary_and_nonempty positive).left
    exact And.intro (unary_e1_inversion (unary_append_left_factor appendUnary))
      (unary_append_right_factor appendUnary)
  · intro factors
    exact PositiveUnaryDenominator_append_unary_tail
      (PositiveUnaryDenominator_e1_iff_unary.mpr factors.left) factors.right

theorem PositiveUnaryDenominator_append_e1_right_iff {head tail : BHist} :
    PositiveUnaryDenominator (BEDC.FKernel.Cont.append head (BHist.e1 tail)) ↔
      UnaryHistory head ∧ UnaryHistory tail := by
  constructor
  · intro positive
    have appendUnary : UnaryHistory (append head tail) :=
      PositiveUnaryDenominator_e1_iff_unary.mp positive
    exact unary_append_factors_iff_result.mpr appendUnary
  · intro factors
    exact PositiveUnaryDenominator_e1_iff_unary.mpr
      (unary_append_closed factors.left factors.right)

end BEDC.Derived.RatUp
