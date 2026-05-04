import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_selected_continuation_e0_endpoint_absurd
    {x y : Nat -> BHist} {n : Nat} {q xq yq zx zy : BHist} :
    RealStreamClassifier x y -> UnaryHistory q -> Cont (x n) q xq -> Cont (y n) q yq ->
      (hsame xq (BHist.e0 zx) -> False) ∧ (hsame yq (BHist.e0 zy) -> False) := by
  intro classified qUnary contX contY
  have positives :
      PositiveUnaryDenominator xq ∧ PositiveUnaryDenominator yq :=
    RealStreamClassifier_selected_continuation_positive_denominators classified qUnary contX contY
  constructor
  · intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.left)
  · intro sameZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero positives.right)

end BEDC.Derived.RealUp
