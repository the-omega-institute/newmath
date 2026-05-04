import BEDC.Derived.RealUp
import BEDC.Derived.RealUp.SelectedContinuationEndpoint

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_selected_continuation_full_shape_package
    {x y : Nat -> BHist} {n : Nat} {q xq yq a b zX zY : BHist} :
    RealStreamClassifier x y -> UnaryHistory q -> Cont (x n) q xq -> Cont (y n) q yq ->
      hsame xq (BHist.e1 a) -> hsame yq (BHist.e1 b) ->
        UnaryHistory a ∧ UnaryHistory b ∧ hsame a b ∧ PositiveUnaryDenominator xq ∧
          PositiveUnaryDenominator yq ∧ UnaryHistory xq ∧ UnaryHistory yq ∧
            (hsame xq BHist.Empty -> False) ∧ (hsame yq BHist.Empty -> False) ∧
              (hsame xq (BHist.e0 zX) -> False) ∧
                (hsame yq (BHist.e0 zY) -> False) := by
  intro classified qUnary contX contY sameX sameY
  have readback :
      UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RealStreamClassifier_selected_continuation_e1_pair_readback classified qUnary contX
      contY sameX sameY
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
  exact And.intro readback.left
    (And.intro readback.right.left
      (And.intro readback.right.right
        (And.intro positives.left
          (And.intro positives.right
            (And.intro leftRows.left
              (And.intro rightRows.left
                (And.intro leftRows.right
                  (And.intro rightRows.right
                    (And.intro
                      (fun sameZero =>
                        PositiveUnaryDenominator_e0_absurd
                          (PositiveUnaryDenominator_hsame_transport sameZero positives.left))
                      (fun sameZero =>
                        PositiveUnaryDenominator_e0_absurd
                          (PositiveUnaryDenominator_hsame_transport sameZero
                            positives.right)))))))))))

theorem RealStreamClassifier_transported_selected_full_shape_readback_package
    {x x' y y' : Nat -> BHist} {n : Nat} {a b zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) -> RealStreamClassifier x y ->
        hsame (x' n) (BHist.e1 a) -> hsame (y' n) (BHist.e1 b) ->
          RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧ UnaryHistory a ∧
            UnaryHistory b ∧ hsame a b ∧ PositiveUnaryDenominator (x' n) ∧
              PositiveUnaryDenominator (y' n) ∧ UnaryHistory (x' n) ∧
                UnaryHistory (y' n) ∧ (hsame (x' n) BHist.Empty -> False) ∧
                  (hsame (y' n) BHist.Empty -> False) ∧
                    (hsame (x' n) (BHist.e0 zX) -> False) ∧
                      (hsame (y' n) (BHist.e0 zY) -> False) := by
  intro sameX sameY classified sameLeft sameRight
  have readback :
      RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧ UnaryHistory a ∧
        UnaryHistory b ∧ hsame a b :=
    RealStreamClassifier_transported_selected_e1_full_readback_package sameX sameY
      classified sameLeft sameRight
  have positivePackage :
      RatHistoryClassifier (x' n) (y' n) ∧ PositiveUnaryDenominator (x' n) ∧
        PositiveUnaryDenominator (y' n) ∧ UnaryHistory (x' n) ∧ UnaryHistory (y' n) ∧
          (hsame (x' n) BHist.Empty -> False) ∧
            (hsame (y' n) BHist.Empty -> False) :=
    RealStreamClassifier_transport_selected_positive_unary_nonempty_package sameX sameY
      classified
  have endpointExclusions :
      (hsame (x' n) (BHist.e0 zX) -> False) ∧
        (hsame (y' n) (BHist.e0 zY) -> False) :=
    RealStreamClassifier_transport_selected_e0_endpoint_absurd (n := n) (zx := zX)
      (zy := zY) sameX sameY classified
  exact And.intro readback.left
    (And.intro readback.right.left
      (And.intro readback.right.right.left
        (And.intro readback.right.right.right
          (And.intro positivePackage.right.left
            (And.intro positivePackage.right.right.left
              (And.intro positivePackage.right.right.right.left
                (And.intro positivePackage.right.right.right.right.left
                  (And.intro positivePackage.right.right.right.right.right.left
                    (And.intro positivePackage.right.right.right.right.right.right
                      (And.intro endpointExclusions.left endpointExclusions.right))))))))))

end BEDC.Derived.RealUp
