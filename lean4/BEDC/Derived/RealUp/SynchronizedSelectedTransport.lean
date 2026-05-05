import BEDC.Derived.RealUp
import BEDC.Derived.RealUp.SelectedTransportReadback

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealSelectedTransport_synchronized_e1_endpoints
    {x x' y y' pX pY tX tY mX mY oX oY : Nat -> BHist} {m n : Nat}
    {a a' b b' zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          UnaryHistory (pX n) ->
            UnaryHistory (tX n) ->
              hsame (pX n) (pY n) ->
                hsame (tX n) (tY n) ->
                  Cont (pX n) (x' n) (mX n) ->
                    Cont (mX n) (tX n) (oX n) ->
                      Cont (pY n) (y' n) (mY n) ->
                        Cont (mY n) (tY n) (oY n) ->
                          hsame (oX n) (BHist.e1 a) ->
                            hsame (oX n) (BHist.e1 a') ->
                              hsame (oY n) (BHist.e1 b) ->
                                hsame (oY n) (BHist.e1 b') ->
                                  hsame (x' n) (BHist.e1 a) ->
                                    hsame (y' n) (BHist.e1 b) ->
                                      RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧
                                        RatHistoryClassifier (BHist.e1 a') (BHist.e1 b') ∧
                                          UnaryHistory a ∧ UnaryHistory a' ∧
                                            UnaryHistory b ∧ UnaryHistory b' ∧
                                              hsame a a' ∧ hsame b b' ∧ hsame a b ∧
                                                hsame a' b' ∧ hsame a b' ∧
                                                  hsame a' b := by
  intro sameX sameY classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont
    oYCont sameOXA sameOXA' sameOYB sameOYB' sameX'A sameY'B
  have pointClassifier : RatHistoryClassifier (x' n) (y' n) :=
    RatHistoryClassifier_hsame_transport (sameX n) (sameY n) (classified n)
  have displayedAB : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameX'A sameY'B pointClassifier
  have readAB : UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RatHistoryClassifier_cont_unary_context_e1_pair_readback pointClassifier pXUnary sameP
      tXUnary sameT pXCont oXCont pYCont oYCont sameOXA sameOYB
  have readA'B' : UnaryHistory a' ∧ UnaryHistory b' ∧ hsame a' b' :=
    RatHistoryClassifier_cont_unary_context_e1_pair_readback pointClassifier pXUnary sameP
      tXUnary sameT pXCont oXCont pYCont oYCont sameOXA' sameOYB'
  have sameAA' : hsame a a' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameOXA) sameOXA')
  have sameBB' : hsame b b' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameOYB) sameOYB')
  have sameAB' : hsame a b' :=
    hsame_trans readAB.right.right sameBB'
  have sameA'B : hsame a' b :=
    hsame_trans (hsame_symm sameAA') readAB.right.right
  have displayedA'B' : RatHistoryClassifier (BHist.e1 a') (BHist.e1 b') :=
    RatHistoryClassifier_e1_tail_unary_iff.mpr
      ⟨readA'B'.left, readA'B'.right.left, readA'B'.right.right⟩
  exact ⟨displayedAB, displayedA'B', readAB.left, readA'B'.left, readAB.right.left,
    readA'B'.right.left, sameAA', sameBB', readAB.right.right, readA'B'.right.right,
    sameAB', sameA'B⟩

theorem RealSelectedTransport_constant_real_classifier_package
    {x x' y y' pX pY tX tY mX mY oX oY : Nat -> BHist} {m n : Nat}
    {a a' b b' zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          UnaryHistory (pX n) ->
            UnaryHistory (tX n) ->
              hsame (pX n) (pY n) ->
                hsame (tX n) (tY n) ->
                  Cont (pX n) (x' n) (mX n) ->
                    Cont (mX n) (tX n) (oX n) ->
                      Cont (pY n) (y' n) (mY n) ->
                        Cont (mY n) (tY n) (oY n) ->
                          hsame (oX n) (BHist.e1 a) ->
                            hsame (oX n) (BHist.e1 a') ->
                              hsame (oY n) (BHist.e1 b) ->
                                hsame (oY n) (BHist.e1 b') ->
                                  hsame (x' n) (BHist.e1 a) ->
                                    hsame (y' n) (BHist.e1 b) ->
                                      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 a))
                                          (BHist.e1 (BHist.e1 b)) ∧
                                        RealConstantHistoryClassifier (BHist.e1 (BHist.e1 a'))
                                            (BHist.e1 (BHist.e1 b')) ∧
                                          hsame a a' ∧ hsame b b' ∧ hsame a b ∧
                                            hsame a' b' ∧ hsame a b' ∧ hsame a' b := by
  intro sameX sameY classified pXUnary tXUnary sameP sameT pXCont oXCont pYCont
    oYCont sameOXA sameOXA' sameOYB sameOYB' sameX'A sameY'B
  have synced :=
    RealSelectedTransport_synchronized_e1_endpoints (m := m) (n := n) (zX := zX)
      (zY := zY) sameX sameY classified pXUnary tXUnary sameP sameT pXCont oXCont
      pYCont oYCont sameOXA sameOXA' sameOYB sameOYB' sameX'A sameY'B
  have realAB :
      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 a)) (BHist.e1 (BHist.e1 b)) :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr synced.left
  have realA'B' :
      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 a'))
        (BHist.e1 (BHist.e1 b')) :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr synced.right.left
  exact ⟨realAB, realA'B', synced.right.right.right.right.right.right.left,
    synced.right.right.right.right.right.right.right.left,
    synced.right.right.right.right.right.right.right.right.left,
    synced.right.right.right.right.right.right.right.right.right.left,
    synced.right.right.right.right.right.right.right.right.right.right.left,
    synced.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.RealUp
