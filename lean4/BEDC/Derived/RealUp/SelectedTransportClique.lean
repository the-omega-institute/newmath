import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealSelectedTransport_synchronized_e1_classifier_clique
    {x x' y y' pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat}
    {a a' b b' : BHist} :
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
    RatHistoryClassifier (BHist.e1 a) (BHist.e1 a') ∧
      RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧
        RatHistoryClassifier (BHist.e1 a) (BHist.e1 b') ∧
          RatHistoryClassifier (BHist.e1 a') (BHist.e1 b) ∧
            RatHistoryClassifier (BHist.e1 a') (BHist.e1 b') ∧
              RatHistoryClassifier (BHist.e1 b) (BHist.e1 b') := by
  intro sameX sameY classified prefixUnary tailUnary samePrefix sameTail contPX contOX
    contPY contOY sameOXA sameOXA' sameOYB sameOYB'
  have transportedPoint : RatHistoryClassifier (x' n) (y' n) :=
    RatHistoryClassifier_hsame_transport (sameX n) (sameY n) (classified n)
  have contextClassified :
      RatHistoryClassifier (append (pX n) (append (x' n) (tX n)))
        (append (pY n) (append (y' n) (tY n))) :=
    RatHistoryClassifier_unary_denominator_context_closed transportedPoint
      prefixUnary samePrefix tailUnary sameTail
  have sameOutX : hsame (append (pX n) (append (x' n) (tX n))) (oX n) := by
    have prefEq : mX n = append (pX n) (x' n) := cont_iff_append.mp contPX
    have outEq : oX n = append (mX n) (tX n) := cont_iff_append.mp contOX
    exact (append_assoc (pX n) (x' n) (tX n)).symm.trans
      ((congrArg (fun h => append h (tX n)) prefEq).symm.trans outEq.symm)
  have sameOutY : hsame (append (pY n) (append (y' n) (tY n))) (oY n) := by
    have prefEq : mY n = append (pY n) (y' n) := cont_iff_append.mp contPY
    have outEq : oY n = append (mY n) (tY n) := cont_iff_append.mp contOY
    exact (append_assoc (pY n) (y' n) (tY n)).symm.trans
      ((congrArg (fun h => append h (tY n)) prefEq).symm.trans outEq.symm)
  have endpointClassified : RatHistoryClassifier (oX n) (oY n) :=
    RatHistoryClassifier_hsame_transport sameOutX sameOutY contextClassified
  have rowAA' : RatHistoryClassifier (BHist.e1 a) (BHist.e1 a') :=
    RatHistoryClassifier_hsame_transport sameOXA sameOXA'
      (RatHistoryClassifier_hsame_transport (hsame_refl (oX n)) (hsame_refl (oX n))
        ⟨endpointClassified.left, endpointClassified.left, hsame_refl (oX n)⟩)
  have rowAB : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameOXA sameOYB
      endpointClassified
  have rowAB' : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b') :=
    RatHistoryClassifier_hsame_transport sameOXA sameOYB'
      endpointClassified
  have rowA'B : RatHistoryClassifier (BHist.e1 a') (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameOXA' sameOYB
      endpointClassified
  have rowA'B' : RatHistoryClassifier (BHist.e1 a') (BHist.e1 b') :=
    RatHistoryClassifier_hsame_transport sameOXA' sameOYB'
      endpointClassified
  have rowBB' : RatHistoryClassifier (BHist.e1 b) (BHist.e1 b') :=
    RatHistoryClassifier_hsame_transport sameOYB sameOYB'
      (RatHistoryClassifier_hsame_transport (hsame_refl (oY n)) (hsame_refl (oY n))
        ⟨endpointClassified.right.left, endpointClassified.right.left, hsame_refl (oY n)⟩)
  exact ⟨rowAA', rowAB, rowAB', rowA'B, rowA'B', rowBB'⟩

end BEDC.Derived.RealUp
