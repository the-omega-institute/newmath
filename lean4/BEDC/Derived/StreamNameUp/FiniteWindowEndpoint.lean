import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamNameFiniteWindowClassifier_selected_zero_head_exclusion
    {s t : BHist -> BHist} {bundle : ProbeBundle BHist} {n zS zT : BHist} :
    RatStreamNameFiniteWindowClassifier s t bundle -> InBundle n bundle -> UnaryHistory n ->
      (hsame (s n) (BHist.e0 zS) -> False) ∧
        (hsame (t n) (BHist.e0 zT) -> False) := by
  intro classified member nUnary
  have selected : RatHistoryClassifier (s n) (t n) :=
    classified n member nUnary
  have positives : PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) :=
    RatHistoryClassifier_positive_denominators selected
  exact And.intro
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.left))
    (fun sameZero =>
      PositiveUnaryDenominator_e0_absurd
        (PositiveUnaryDenominator_hsame_transport sameZero positives.right))

end BEDC.Derived.StreamNameUp
