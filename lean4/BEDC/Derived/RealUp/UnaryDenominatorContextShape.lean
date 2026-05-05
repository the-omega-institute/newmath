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

theorem RealStreamClassifier_transported_unary_denominator_context_closed
    {x x' y y' pX pY tX tY mX mY oX oY : Nat -> BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          (forall i : Nat, UnaryHistory (pX i)) ->
            (forall i : Nat, UnaryHistory (tX i)) ->
              (forall i : Nat, hsame (pX i) (pY i)) ->
                (forall i : Nat, hsame (tX i) (tY i)) ->
                  (forall i : Nat, Cont (pX i) (x' i) (mX i)) ->
                    (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                      (forall i : Nat, Cont (pY i) (y' i) (mY i)) ->
                        (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                          RealStreamClassifier oX oY := by
  intro sameX sameY classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont
  have transported : RealStreamClassifier x' y' := by
    intro i
    exact RatHistoryClassifier_hsame_transport (sameX i) (sameY i) (classified i)
  exact RealStreamClassifier_unary_denominator_context_closed transported pXUnary tXUnary
    sameP sameT pXCont oXCont pYCont oYCont

theorem RealSelectedTransport_common_rational_classifier_class
    {x x' y y' pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat}
    {a a' b b' : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          (forall i : Nat, UnaryHistory (pX i)) ->
            (forall i : Nat, UnaryHistory (tX i)) ->
              (forall i : Nat, hsame (pX i) (pY i)) ->
                (forall i : Nat, hsame (tX i) (tY i)) ->
                  (forall i : Nat, Cont (pX i) (x' i) (mX i)) ->
                    (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                      (forall i : Nat, Cont (pY i) (y' i) (mY i)) ->
                        (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                          hsame (oX n) (BHist.e1 a) ->
                            hsame (oX n) (BHist.e1 a') ->
                              hsame (oY n) (BHist.e1 b) ->
                                hsame (oY n) (BHist.e1 b') ->
                                  hsame (x' n) (BHist.e1 a) ->
                                    hsame (y' n) (BHist.e1 b) ->
                                      RatHistoryClassifier (oX n) (BHist.e1 a) ∧
                                        RatHistoryClassifier (oY n) (BHist.e1 a) ∧
                                          RatHistoryClassifier (x' n) (BHist.e1 a) ∧
                                            RatHistoryClassifier (y' n) (BHist.e1 a) ∧
                                              RatHistoryClassifier (BHist.e1 a')
                                                (BHist.e1 a) ∧
                                                RatHistoryClassifier (BHist.e1 b)
                                                  (BHist.e1 a) ∧
                                                  RatHistoryClassifier (BHist.e1 b')
                                                    (BHist.e1 a) := by
  intro sameX sameY classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont
    oYCont sameOX sameOX' sameOY sameOY' sameX' sameY'
  have contextClassified : RealStreamClassifier oX oY :=
    RealStreamClassifier_transported_unary_denominator_context_closed sameX sameY classified
      pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameOX sameOY (contextClassified n)
  have centered : RatHistoryClassifier (BHist.e1 a) (BHist.e1 a) :=
    RatHistoryClassifier_trans displayed (RatHistoryClassifier_symm displayed)
  have outXClass : RatHistoryClassifier (oX n) (BHist.e1 a) :=
    RatHistoryClassifier_hsame_transport (hsame_symm sameOX) (hsame_refl (BHist.e1 a))
      centered
  have outYClass : RatHistoryClassifier (oY n) (BHist.e1 a) :=
    RatHistoryClassifier_hsame_transport (hsame_symm sameOY) (hsame_refl (BHist.e1 a))
      (RatHistoryClassifier_symm displayed)
  have sourceXClass : RatHistoryClassifier (x' n) (BHist.e1 a) :=
    RatHistoryClassifier_hsame_transport (hsame_symm sameX') (hsame_refl (BHist.e1 a))
      centered
  have sourceYClass : RatHistoryClassifier (y' n) (BHist.e1 a) :=
    RatHistoryClassifier_hsame_transport (hsame_symm sameY') (hsame_refl (BHist.e1 a))
      (RatHistoryClassifier_symm displayed)
  have aPrimeClass : RatHistoryClassifier (BHist.e1 a') (BHist.e1 a) :=
    RatHistoryClassifier_hsame_transport sameOX' (hsame_refl (BHist.e1 a))
      outXClass
  have bClass : RatHistoryClassifier (BHist.e1 b) (BHist.e1 a) :=
    RatHistoryClassifier_symm displayed
  have bPrimeClass : RatHistoryClassifier (BHist.e1 b') (BHist.e1 a) :=
    RatHistoryClassifier_hsame_transport sameOY' (hsame_refl (BHist.e1 a))
      outYClass
  exact And.intro outXClass
    (And.intro outYClass
      (And.intro sourceXClass
        (And.intro sourceYClass
          (And.intro aPrimeClass (And.intro bClass bPrimeClass)))))

theorem RealStreamClassifier_unary_denominator_context_appended_e0_tail_absurd
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat}
    {dX dY zX zY : BHist} :
    RealStreamClassifier x y ->
      (forall i : Nat, UnaryHistory (pX i)) ->
        (forall i : Nat, UnaryHistory (tX i)) ->
          (forall i : Nat, hsame (pX i) (pY i)) ->
            (forall i : Nat, hsame (tX i) (tY i)) ->
              (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
                (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                  (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                    (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                      (hsame (oX n) (append dX (BHist.e0 zX)) -> False) ∧
                        (hsame (oY n) (append dY (BHist.e0 zY)) -> False) := by
  intro classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont
  have positives :
      PositiveUnaryDenominator (oX n) ∧ PositiveUnaryDenominator (oY n) :=
    RealStreamClassifier_unary_denominator_context_selected_positive_denominators (n := n)
      classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont
  constructor
  · intro displayed
    exact PositiveUnaryDenominator_append_e0_tail_absurd
      (PositiveUnaryDenominator_hsame_transport displayed positives.left)
  · intro displayed
    exact PositiveUnaryDenominator_append_e0_tail_absurd
      (PositiveUnaryDenominator_hsame_transport displayed positives.right)

theorem RealStreamClassifier_unary_denominator_context_selected_e1_tail_determinacy
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat}
    {a a' b b' : BHist} :
    RealStreamClassifier x y ->
      (forall i : Nat, UnaryHistory (pX i)) ->
        (forall i : Nat, UnaryHistory (tX i)) ->
          (forall i : Nat, hsame (pX i) (pY i)) ->
            (forall i : Nat, hsame (tX i) (tY i)) ->
              (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
                (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                  (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                    (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                      hsame (oX n) (BHist.e1 a) -> hsame (oX n) (BHist.e1 a') ->
                        hsame (oY n) (BHist.e1 b) -> hsame (oY n) (BHist.e1 b') ->
                          UnaryHistory a ∧ UnaryHistory a' ∧ UnaryHistory b ∧
                            UnaryHistory b' ∧ hsame a a' ∧ hsame b b' ∧ hsame a b ∧
                              hsame a' b' := by
  intro classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont sameLeft
    sameLeft' sameRight sameRight'
  have readAB :
      UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RealStreamClassifier_unary_denominator_context_selected_e1_pair_readback (n := n)
      classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont sameLeft
      sameRight
  have readA'B' :
      UnaryHistory a' ∧ UnaryHistory b' ∧ hsame a' b' :=
    RealStreamClassifier_unary_denominator_context_selected_e1_pair_readback (n := n)
      classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont sameLeft'
      sameRight'
  have sameAA' : hsame a a' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameLeft) sameLeft')
  have sameBB' : hsame b b' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameRight) sameRight')
  exact And.intro readAB.left
    (And.intro readA'B'.left
      (And.intro readAB.right.left
        (And.intro readA'B'.right.left
          (And.intro sameAA'
            (And.intro sameBB' (And.intro readAB.right.right readA'B'.right.right))))))

theorem RealStreamClassifier_unary_denominator_context_selected_e1_tail_pairwise_coherence
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat}
    {a a' b b' : BHist} :
    RealStreamClassifier x y ->
      (forall i : Nat, UnaryHistory (pX i)) ->
        (forall i : Nat, UnaryHistory (tX i)) ->
          (forall i : Nat, hsame (pX i) (pY i)) ->
            (forall i : Nat, hsame (tX i) (tY i)) ->
              (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
                (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                  (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                    (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                      hsame (oX n) (BHist.e1 a) -> hsame (oX n) (BHist.e1 a') ->
                        hsame (oY n) (BHist.e1 b) -> hsame (oY n) (BHist.e1 b') ->
                          UnaryHistory a ∧ UnaryHistory a' ∧ UnaryHistory b ∧
                            UnaryHistory b' ∧ hsame a a' ∧ hsame a b ∧
                              hsame a b' ∧ hsame a' b ∧ hsame a' b' ∧
                                hsame b b' := by
  intro classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont sameLeft
    sameLeft' sameRight sameRight'
  have det :=
    RealStreamClassifier_unary_denominator_context_selected_e1_tail_determinacy
      (n := n) classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont oYCont
      sameLeft sameLeft' sameRight sameRight'
  have sameAA' : hsame a a' := det.right.right.right.right.left
  have sameBB' : hsame b b' := det.right.right.right.right.right.left
  have sameAB : hsame a b := det.right.right.right.right.right.right.left
  have sameA'B' : hsame a' b' := det.right.right.right.right.right.right.right
  have sameAB' : hsame a b' := hsame_trans sameAB sameBB'
  have sameA'B : hsame a' b := hsame_trans (hsame_symm sameAA') sameAB
  exact ⟨det.left, det.right.left, det.right.right.left, det.right.right.right.left,
    sameAA', sameAB, sameAB', sameA'B, sameA'B', sameBB'⟩

end BEDC.Derived.RealUp
