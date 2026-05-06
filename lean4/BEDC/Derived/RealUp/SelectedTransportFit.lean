import BEDC.Derived.RealUp.SelectedContextualEndpoint
import BEDC.Derived.RealUp.SelectedTransportReadback

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealSelectedTransportFit_certificate
    {x x' y y' pX pY tX tY mX mY oX oY : Nat -> BHist} {m n : Nat}
    {a a' b b' zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          RealStreamPrefixClassifier x y (m + n) ->
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
                                        RatHistoryClassifier (oX n) (oY n) ∧
                                          RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧
                                            UnaryHistory a ∧ UnaryHistory a' ∧
                                              UnaryHistory b ∧ UnaryHistory b' ∧
                                                hsame a a' ∧ hsame b b' ∧
                                                  hsame a b ∧ hsame a' b' ∧
                                                    PositiveUnaryDenominator (x' n) ∧
                                                      PositiveUnaryDenominator (y' n) ∧
                                                        Cont (pX n) (x' n) (mX n) := by
  intro sameX sameY streamClassified prefixClassified prefUnary tailUnary prefSame tailSame
    prefXCont outXCont prefYCont outYCont outXOne outXOne' outYOne outYOne'
    selectedXOne selectedYOne
  have contextual :=
    RealStreamClassifier_transported_contextual_displayed_e1_classifier_package
      (zX := zX) (zY := zY) sameX sameY streamClassified prefUnary tailUnary prefSame
      tailSame prefXCont outXCont prefYCont outYCont outXOne outYOne
  have tails :=
    RealStreamClassifier_transported_contextual_e1_tail_determinacy sameX sameY
      streamClassified prefUnary tailUnary prefSame tailSame prefXCont outXCont prefYCont
      outYCont outXOne outXOne' outYOne outYOne'
  have selected :=
    RealStreamPrefixClassifier_transported_selected_full_shape_readback_package
      (zX := zX) (zY := zY) prefixClassified sameX sameY selectedXOne selectedYOne
  exact
    ⟨contextual.left, contextual.right.left, tails.left, tails.right.left,
      tails.right.right.left, tails.right.right.right.left, tails.right.right.right.right.left,
      tails.right.right.right.right.right.left, tails.right.right.right.right.right.right.left,
      tails.right.right.right.right.right.right.right, selected.right.right.right.right.left,
      selected.right.right.right.right.right.left, prefXCont⟩

theorem RealSelectedTransportFit_appended_tail_certificate
    {x x' y y' pX pY tX tY mX mY oX oY : Nat -> BHist} {m n : Nat}
    {a a' b b' dX dY eX eY wX wY zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y ->
          RealStreamPrefixClassifier x y (m + n) ->
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
                                        (RatHistoryClassifier (oX n) (oY n) ∧
                                          RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧
                                            UnaryHistory a ∧ UnaryHistory a' ∧
                                              UnaryHistory b ∧ UnaryHistory b' ∧
                                                hsame a a' ∧ hsame b b' ∧
                                                  hsame a b ∧ hsame a' b' ∧
                                                    PositiveUnaryDenominator (x' n) ∧
                                                      PositiveUnaryDenominator (y' n) ∧
                                                        Cont (pX n) (x' n) (mX n)) ∧
                                          (hsame (oX n) (append dX (BHist.e0 zX)) -> False) ∧
                                            (hsame (oY n) (append dY (BHist.e0 zY)) -> False) ∧
                                              (hsame (x' n) (append eX (BHist.e0 wX)) -> False) ∧
                                                (hsame (y' n) (append eY (BHist.e0 wY)) ->
                                                  False) := by
  intro sameX sameY streamClassified prefixClassified prefUnary tailUnary prefSame tailSame
    prefXCont outXCont prefYCont outYCont outXOne outXOne' outYOne outYOne'
    selectedXOne selectedYOne
  have package :=
    RealSelectedTransportFit_certificate (zX := zX) (zY := zY) sameX sameY
      streamClassified prefixClassified prefUnary tailUnary prefSame tailSame prefXCont
      outXCont prefYCont outYCont outXOne outXOne' outYOne outYOne' selectedXOne
      selectedYOne
  have outputPositive :
      PositiveUnaryDenominator (oX n) ∧ PositiveUnaryDenominator (oY n) :=
    RatHistoryClassifier_positive_denominators package.left
  exact And.intro package
    (And.intro
      (fun sameTail =>
        PositiveUnaryDenominator_append_e0_tail_absurd
          (PositiveUnaryDenominator_hsame_transport sameTail outputPositive.left))
      (And.intro
        (fun sameTail =>
          PositiveUnaryDenominator_append_e0_tail_absurd
            (PositiveUnaryDenominator_hsame_transport sameTail outputPositive.right))
        (And.intro
          (fun sameTail =>
            PositiveUnaryDenominator_append_e0_tail_absurd
              (PositiveUnaryDenominator_hsame_transport sameTail
                package.right.right.right.right.right.right.right.right.right.right.left))
          (fun sameTail =>
            PositiveUnaryDenominator_append_e0_tail_absurd
              (PositiveUnaryDenominator_hsame_transport sameTail
                package.right.right.right.right.right.right.right.right.right.right.right.left)))))

end BEDC.Derived.RealUp
