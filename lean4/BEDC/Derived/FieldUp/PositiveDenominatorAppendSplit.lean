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

theorem RatHistoryCarrier_append_split {h k : BHist} :
    RatHistoryCarrier (append h k) -> RatHistoryCarrier h ∨ RatHistoryCarrier k := by
  intro carrier
  have positive : PositiveUnaryDenominator (append h k) :=
    RatHistoryCarrier_iff_positive_denominator.mp carrier
  have split := field_positive_denominator_append_split positive
  cases split with
  | inl positiveH =>
      exact Or.inl (RatHistoryCarrier_iff_positive_denominator.mpr positiveH)
  | inr positiveK =>
      exact Or.inr (RatHistoryCarrier_iff_positive_denominator.mpr positiveK)

theorem RatHistoryClassifier_append_left_split {h k d : BHist} :
    RatHistoryClassifier (append h k) d -> RatHistoryCarrier h ∨ RatHistoryCarrier k := by
  intro classified
  exact RatHistoryCarrier_append_split classified.left

end BEDC.Derived.FieldUp
