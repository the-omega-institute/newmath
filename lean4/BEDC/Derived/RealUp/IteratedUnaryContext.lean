import BEDC.Derived.RealUp.UnaryDenominatorContextShape

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RealStreamClassifier_transported_iterated_unary_context_selected_e1_tail_pairwise_coherence
    {x x' y y' pX pY tX tY mX mY uX uY qX qY sX sY vX vY oX oY : Nat -> BHist}
    {n : Nat} {a a' b b' : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          (forall i : Nat, UnaryHistory (pX i)) ->
            (forall i : Nat, UnaryHistory (tX i)) ->
              (forall i : Nat, hsame (pX i) (pY i)) ->
                (forall i : Nat, hsame (tX i) (tY i)) ->
                  (forall i : Nat, Cont (pX i) (x' i) (mX i)) ->
                    (forall i : Nat, Cont (mX i) (tX i) (uX i)) ->
                      (forall i : Nat, Cont (pY i) (y' i) (mY i)) ->
                        (forall i : Nat, Cont (mY i) (tY i) (uY i)) ->
                          (forall i : Nat, UnaryHistory (qX i)) ->
                            (forall i : Nat, UnaryHistory (sX i)) ->
                              (forall i : Nat, hsame (qX i) (qY i)) ->
                                (forall i : Nat, hsame (sX i) (sY i)) ->
                                  (forall i : Nat, Cont (qX i) (uX i) (vX i)) ->
                                    (forall i : Nat, Cont (vX i) (sX i) (oX i)) ->
                                      (forall i : Nat, Cont (qY i) (uY i) (vY i)) ->
                                        (forall i : Nat, Cont (vY i) (sY i) (oY i)) ->
                                          hsame (oX n) (BHist.e1 a) ->
                                            hsame (oX n) (BHist.e1 a') ->
                                              hsame (oY n) (BHist.e1 b) ->
                                                hsame (oY n) (BHist.e1 b') ->
                                                  UnaryHistory a ∧ UnaryHistory a' ∧
                                                    UnaryHistory b ∧ UnaryHistory b' ∧
                                                      hsame a a' ∧ hsame a b ∧
                                                        hsame a b' ∧ hsame a' b ∧
                                                          hsame a' b' ∧ hsame b b' := by
  intro sameX sameY classified pXUnary tXUnary sameP sameT pXCont uXCont pYCont
    uYCont qXUnary sXUnary sameQ sameS qXCont oXCont qYCont oYCont sameOX sameOX'
    sameOY sameOY'
  have firstLayer : RealStreamClassifier uX uY :=
    RealStreamClassifier_transported_unary_denominator_context_closed sameX sameY classified
      pXUnary tXUnary sameP sameT pXCont uXCont pYCont uYCont
  have tailsAB :
      UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RealStreamClassifier_unary_denominator_context_e1_pair_readback (n := n) firstLayer
      qXUnary sXUnary sameQ sameS qXCont oXCont qYCont oYCont sameOX sameOY
  have tailsA'B :
      UnaryHistory a' ∧ UnaryHistory b ∧ hsame a' b :=
    RealStreamClassifier_unary_denominator_context_e1_pair_readback (n := n) firstLayer
      qXUnary sXUnary sameQ sameS qXCont oXCont qYCont oYCont sameOX' sameOY
  have tailsAB' :
      UnaryHistory a ∧ UnaryHistory b' ∧ hsame a b' :=
    RealStreamClassifier_unary_denominator_context_e1_pair_readback (n := n) firstLayer
      qXUnary sXUnary sameQ sameS qXCont oXCont qYCont oYCont sameOX sameOY'
  have sameAA' : hsame a a' := by
    exact Iff.mp hsame_e1_iff (hsame_trans (hsame_symm sameOX) sameOX')
  have sameBB' : hsame b b' := by
    exact Iff.mp hsame_e1_iff (hsame_trans (hsame_symm sameOY) sameOY')
  have sameA'B' : hsame a' b' :=
    hsame_trans (hsame_symm sameAA') tailsAB'.right.right
  exact And.intro tailsAB.left
    (And.intro tailsA'B.left
      (And.intro tailsAB.right.left
        (And.intro tailsAB'.right.left
          (And.intro sameAA'
            (And.intro tailsAB.right.right
              (And.intro tailsAB'.right.right
                (And.intro tailsA'B.right.right
                  (And.intro sameA'B' sameBB'))))))))

end BEDC.Derived.RealUp
