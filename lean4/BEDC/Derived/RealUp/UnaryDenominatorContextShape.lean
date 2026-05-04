import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_unary_denominator_context_selected_classifier_shape_package
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat} {zX zY : BHist} :
    RealStreamClassifier x y ->
      (forall i : Nat, UnaryHistory (pX i)) ->
        (forall i : Nat, UnaryHistory (tX i)) ->
          (forall i : Nat, hsame (pX i) (pY i)) ->
            (forall i : Nat, hsame (tX i) (tY i)) ->
              (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
                (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                  (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                    (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                      RatHistoryClassifier (oX n) (oY n) ∧
                        PositiveUnaryDenominator (oX n) ∧
                          PositiveUnaryDenominator (oY n) ∧
                            UnaryHistory (oX n) ∧ UnaryHistory (oY n) ∧
                              (hsame (oX n) BHist.Empty -> False) ∧
                                (hsame (oY n) BHist.Empty -> False) ∧
                                  (hsame (oX n) (BHist.e0 zX) -> False) ∧
                                    (hsame (oY n) (BHist.e0 zY) -> False) := by
  intro classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont
  have contextClassified : RealStreamClassifier oX oY :=
    RealStreamClassifier_unary_denominator_context_closed classified pXUnary tXUnary sameP
      sameT pXCont oXCont pYCont oYCont
  have positives :
      PositiveUnaryDenominator (oX n) ∧ PositiveUnaryDenominator (oY n) :=
    RealStreamClassifier_unary_denominator_context_selected_positive_denominators (n := n)
      classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont
  have shape :
      UnaryHistory (oX n) ∧ UnaryHistory (oY n) ∧
        (hsame (oX n) BHist.Empty -> False) ∧
          (hsame (oY n) BHist.Empty -> False) ∧
            (hsame (oX n) (BHist.e0 zX) -> False) ∧
              (hsame (oY n) (BHist.e0 zY) -> False) :=
    RealStreamClassifier_unary_denominator_context_selected_shape_package (n := n)
      (zx := zX) (zy := zY) classified pXUnary tXUnary sameP sameT pXCont oXCont
      pYCont oYCont
  exact And.intro (contextClassified n)
    (And.intro positives.left
      (And.intro positives.right
        (And.intro shape.left
          (And.intro shape.right.left
            (And.intro shape.right.right.left
              (And.intro shape.right.right.right.left
                (And.intro shape.right.right.right.right.left
                  shape.right.right.right.right.right)))))))

end BEDC.Derived.RealUp
