import BEDC.Derived.RatUp.DenominatorAppendDecomposition
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatHistoryCarrier_append_split {h k : BHist} :
    RatHistoryCarrier (append h k) -> RatHistoryCarrier h ∨ RatHistoryCarrier k := by
  intro carrier
  have positive : PositiveUnaryDenominator (append h k) :=
    RatHistoryCarrier_iff_positive_denominator.mp carrier
  have split := PositiveUnaryDenominator_append_factor_or_tail positive
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
