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

theorem RealStreamClassifier_selected_continuation_endpoint_boundary_package
    {x y : Nat -> BHist} {n : Nat} {q xq yq zX zY : BHist} :
    RealStreamClassifier x y -> UnaryHistory q -> Cont (x n) q xq -> Cont (y n) q yq ->
      PositiveUnaryDenominator xq ∧ PositiveUnaryDenominator yq ∧ UnaryHistory xq ∧
        UnaryHistory yq ∧ (hsame xq BHist.Empty -> False) ∧
          (hsame yq BHist.Empty -> False) ∧ (hsame xq (BHist.e0 zX) -> False) ∧
            (hsame yq (BHist.e0 zY) -> False) := by
  intro classified qUnary contX contY
  have positives :
      PositiveUnaryDenominator xq ∧ PositiveUnaryDenominator yq :=
    RealStreamClassifier_selected_continuation_positive_denominators classified qUnary contX
      contY
  have leftRows :
      UnaryHistory xq ∧ (hsame xq BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows :
      UnaryHistory yq ∧ (hsame yq BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  have endpointRows :
      (hsame xq (BHist.e0 zX) -> False) ∧ (hsame yq (BHist.e0 zY) -> False) :=
    RealStreamClassifier_selected_continuation_e0_endpoint_absurd (zx := zX) (zy := zY)
      classified qUnary contX contY
  exact And.intro positives.left
    (And.intro positives.right
      (And.intro leftRows.left
        (And.intro rightRows.left
          (And.intro leftRows.right
            (And.intro rightRows.right
              (And.intro endpointRows.left endpointRows.right))))))

end BEDC.Derived.RealUp
