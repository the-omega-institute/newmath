import BEDC.Derived.RatUp.DenominatorContext

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RatHistoryClassifier_unary_context_e0_endpoint_absurd
    {d e prefD prefE tailD tailE z z' : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      UnaryHistory tailD -> hsame tailD tailE ->
        ((hsame (append prefD (append d tailD)) (BHist.e0 z) -> False) ∧
          (hsame (append prefE (append e tailE)) (BHist.e0 z') -> False)) := by
  intro classified prefDUnary samePref tailDUnary sameTail
  have positives :=
    RatHistoryClassifier_unary_denominator_context_positive_denominators classified
      prefDUnary samePref tailDUnary sameTail
  constructor
  · intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.left)
  · intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.right)

end BEDC.Derived.RatUp
