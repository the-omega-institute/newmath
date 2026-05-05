import BEDC.Derived.RealUp.PrefixTruncation

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_selected_contextual_full_endpoint_package
    {x y prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {n : Nat}
    {leftTail rightTail zX zY : BHist} :
    RealStreamClassifier x y -> UnaryHistory (prefX n) ->
      UnaryHistory (tailX n) -> hsame (prefX n) (prefY n) ->
        hsame (tailX n) (tailY n) -> Cont (prefX n) (x n) (midX n) ->
          Cont (midX n) (tailX n) (outX n) -> Cont (prefY n) (y n) (midY n) ->
            Cont (midY n) (tailY n) (outY n) ->
              hsame (outX n) (BHist.e1 leftTail) ->
                hsame (outY n) (BHist.e1 rightTail) ->
                  RatHistoryClassifier (outX n) (outY n) ∧
                    PositiveUnaryDenominator (outX n) ∧ PositiveUnaryDenominator (outY n) ∧
                      UnaryHistory (outX n) ∧ UnaryHistory (outY n) ∧
                        (hsame (outX n) BHist.Empty -> False) ∧
                          (hsame (outY n) BHist.Empty -> False) ∧
                            (hsame (outX n) (BHist.e0 zX) -> False) ∧
                              (hsame (outY n) (BHist.e0 zY) -> False) ∧
                                UnaryHistory leftTail ∧ UnaryHistory rightTail ∧
                                  hsame leftTail rightTail := by
  intro classified prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont
    outYCont outXOne outYOne
  have prefixClassified : RealStreamPrefixClassifier x y (0 + n) := by
    simp only [Nat.zero_add]
    exact RealStreamClassifier_prefix classified n
  exact RealStreamPrefixClassifier_contextual_full_endpoint_package
    (m := 0) (n := n) prefixClassified prefUnary tailUnary prefSame tailSame prefCont
    outXCont prefYCont outYCont outXOne outYOne

theorem RealStreamClassifier_transported_contextual_full_endpoint_package
    {x x' y y' prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {n : Nat}
    {leftTail rightTail zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y -> UnaryHistory (prefX n) ->
          UnaryHistory (tailX n) -> hsame (prefX n) (prefY n) ->
            hsame (tailX n) (tailY n) -> Cont (prefX n) (x' n) (midX n) ->
              Cont (midX n) (tailX n) (outX n) -> Cont (prefY n) (y' n) (midY n) ->
                Cont (midY n) (tailY n) (outY n) ->
                  hsame (outX n) (BHist.e1 leftTail) ->
                    hsame (outY n) (BHist.e1 rightTail) ->
                      RatHistoryClassifier (outX n) (outY n) ∧
                        PositiveUnaryDenominator (outX n) ∧ PositiveUnaryDenominator (outY n) ∧
                          UnaryHistory (outX n) ∧ UnaryHistory (outY n) ∧
                            (hsame (outX n) BHist.Empty -> False) ∧
                              (hsame (outY n) BHist.Empty -> False) ∧
                                (hsame (outX n) (BHist.e0 zX) -> False) ∧
                                  (hsame (outY n) (BHist.e0 zY) -> False) ∧
                                    UnaryHistory leftTail ∧ UnaryHistory rightTail ∧
                                      hsame leftTail rightTail := by
  intro sameX sameY classified prefUnary tailUnary prefSame tailSame prefCont outXCont
    prefYCont outYCont outXOne outYOne
  have transported : RealStreamClassifier x' y' := by
    intro i
    exact RatHistoryClassifier_hsame_transport (sameX i) (sameY i) (classified i)
  exact RealStreamClassifier_selected_contextual_full_endpoint_package transported prefUnary
    tailUnary prefSame tailSame prefCont outXCont prefYCont outYCont outXOne outYOne

theorem RealStreamClassifier_transported_contextual_displayed_e1_classifier_package
    {x x' y y' prefX prefY tailX tailY midX midY outX outY : Nat -> BHist}
    {n : Nat} {a b zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y -> UnaryHistory (prefX n) -> UnaryHistory (tailX n) ->
          hsame (prefX n) (prefY n) -> hsame (tailX n) (tailY n) ->
            Cont (prefX n) (x' n) (midX n) -> Cont (midX n) (tailX n) (outX n) ->
              Cont (prefY n) (y' n) (midY n) -> Cont (midY n) (tailY n) (outY n) ->
                hsame (outX n) (BHist.e1 a) -> hsame (outY n) (BHist.e1 b) ->
                  RatHistoryClassifier (outX n) (outY n) ∧
                    RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧ UnaryHistory a ∧
                      UnaryHistory b ∧ hsame a b ∧ PositiveUnaryDenominator (outX n) ∧
                        PositiveUnaryDenominator (outY n) ∧ UnaryHistory (outX n) ∧
                          UnaryHistory (outY n) ∧ (hsame (outX n) BHist.Empty -> False) ∧
                            (hsame (outY n) BHist.Empty -> False) ∧
                              (hsame (outX n) (BHist.e0 zX) -> False) ∧
                                (hsame (outY n) (BHist.e0 zY) -> False) := by
  intro sameX sameY classified prefUnary tailUnary prefSame tailSame prefCont outXCont
    prefYCont outYCont outXOne outYOne
  have endpointPackage := RealStreamClassifier_transported_contextual_full_endpoint_package
    (leftTail := a) (rightTail := b) (zX := zX) (zY := zY) sameX sameY classified
    prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont outYCont outXOne
    outYOne
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport outXOne outYOne endpointPackage.left
  exact And.intro endpointPackage.left
    (And.intro displayed
      (And.intro endpointPackage.right.right.right.right.right.right.right.right.right.left
        (And.intro
          endpointPackage.right.right.right.right.right.right.right.right.right.right.left
          (And.intro
            endpointPackage.right.right.right.right.right.right.right.right.right.right.right
            (And.intro endpointPackage.right.left
              (And.intro endpointPackage.right.right.left
                (And.intro endpointPackage.right.right.right.left
                  (And.intro endpointPackage.right.right.right.right.left
                    (And.intro endpointPackage.right.right.right.right.right.left
                      (And.intro endpointPackage.right.right.right.right.right.right.left
                        (And.intro endpointPackage.right.right.right.right.right.right.right.left
                          endpointPackage.right.right.right.right.right.right.right.right.left)))))))))))

theorem RealStreamClassifier_transported_contextual_displayed_e1_appended_tail_exclusion_package
    {x x' y y' prefX prefY tailX tailY midX midY outX outY : Nat -> BHist}
    {n : Nat} {a b dX dY zX zY : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y -> UnaryHistory (prefX n) -> UnaryHistory (tailX n) ->
          hsame (prefX n) (prefY n) -> hsame (tailX n) (tailY n) ->
            Cont (prefX n) (x' n) (midX n) -> Cont (midX n) (tailX n) (outX n) ->
              Cont (prefY n) (y' n) (midY n) -> Cont (midY n) (tailY n) (outY n) ->
                hsame (outX n) (BHist.e1 a) -> hsame (outY n) (BHist.e1 b) ->
                  RatHistoryClassifier (outX n) (outY n) ∧
                    RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) ∧ UnaryHistory a ∧
                      UnaryHistory b ∧ hsame a b ∧ PositiveUnaryDenominator (outX n) ∧
                        PositiveUnaryDenominator (outY n) ∧ UnaryHistory (outX n) ∧
                          UnaryHistory (outY n) ∧ (hsame (outX n) BHist.Empty -> False) ∧
                            (hsame (outY n) BHist.Empty -> False) ∧
                              (hsame (outX n) (BHist.e0 zX) -> False) ∧
                                (hsame (outY n) (BHist.e0 zY) -> False) ∧
                                  (hsame (outX n) (append dX (BHist.e0 zX)) -> False) ∧
                                    (hsame (outY n) (append dY (BHist.e0 zY)) -> False) := by
  intro sameX sameY classified prefUnary tailUnary prefSame tailSame prefCont outXCont
    prefYCont outYCont outXOne outYOne
  have package := RealStreamClassifier_transported_contextual_displayed_e1_classifier_package
    (zX := zX) (zY := zY) sameX sameY classified prefUnary tailUnary prefSame tailSame
    prefCont outXCont prefYCont outYCont outXOne outYOne
  exact ⟨package.left, package.right.left, package.right.right.left,
    package.right.right.right.left, package.right.right.right.right.left,
    package.right.right.right.right.right.left,
    package.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.right.right.left,
    package.right.right.right.right.right.right.right.right.right.right.right.right,
    (fun sameAppendedZero =>
      PositiveUnaryDenominator_append_e0_tail_absurd
        (PositiveUnaryDenominator_hsame_transport sameAppendedZero
          package.right.right.right.right.right.left)),
    (fun sameAppendedZero =>
      PositiveUnaryDenominator_append_e0_tail_absurd
        (PositiveUnaryDenominator_hsame_transport sameAppendedZero
          package.right.right.right.right.right.right.left))⟩

theorem RealStreamClassifier_transported_contextual_e1_tail_determinacy
    {x x' y y' prefX prefY tailX tailY midX midY outX outY : Nat -> BHist}
    {n : Nat} {a a' b b' : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y -> UnaryHistory (prefX n) -> UnaryHistory (tailX n) ->
          hsame (prefX n) (prefY n) -> hsame (tailX n) (tailY n) ->
            Cont (prefX n) (x' n) (midX n) -> Cont (midX n) (tailX n) (outX n) ->
              Cont (prefY n) (y' n) (midY n) -> Cont (midY n) (tailY n) (outY n) ->
                hsame (outX n) (BHist.e1 a) -> hsame (outX n) (BHist.e1 a') ->
                  hsame (outY n) (BHist.e1 b) -> hsame (outY n) (BHist.e1 b') ->
                    UnaryHistory a ∧ UnaryHistory a' ∧ UnaryHistory b ∧ UnaryHistory b' ∧
                      hsame a a' ∧ hsame b b' ∧ hsame a b ∧ hsame a' b' := by
  intro sameX sameY classified prefUnary tailUnary prefSame tailSame prefCont outXCont
    prefYCont outYCont outXOne outXOne' outYOne outYOne'
  have first := RealStreamClassifier_transported_contextual_full_endpoint_package
    (leftTail := a) (rightTail := b) (zX := a) (zY := b) sameX sameY classified
    prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont outYCont
    outXOne outYOne
  have second := RealStreamClassifier_transported_contextual_full_endpoint_package
    (leftTail := a') (rightTail := b') (zX := a') (zY := b') sameX sameY classified
    prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont outYCont
    outXOne' outYOne'
  have firstTails := first.right.right.right.right.right.right.right.right.right
  have secondTails := second.right.right.right.right.right.right.right.right.right
  have sameAA' : hsame a a' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm outXOne) outXOne')
  have sameBB' : hsame b b' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm outYOne) outYOne')
  exact And.intro firstTails.left
    (And.intro secondTails.left
      (And.intro firstTails.right.left
        (And.intro secondTails.right.left
          (And.intro sameAA'
            (And.intro sameBB'
              (And.intro firstTails.right.right secondTails.right.right))))))

theorem RealStreamClassifier_transported_contextual_e1_tail_cross_hsame
    {x x' y y' prefX prefY tailX tailY midX midY outX outY : Nat -> BHist}
    {n : Nat} {a a' b b' : BHist} :
    (forall i : Nat, hsame (x i) (x' i)) ->
      (forall i : Nat, hsame (y i) (y' i)) ->
        RealStreamClassifier x y -> UnaryHistory (prefX n) -> UnaryHistory (tailX n) ->
          hsame (prefX n) (prefY n) -> hsame (tailX n) (tailY n) ->
            Cont (prefX n) (x' n) (midX n) -> Cont (midX n) (tailX n) (outX n) ->
              Cont (prefY n) (y' n) (midY n) -> Cont (midY n) (tailY n) (outY n) ->
                hsame (outX n) (BHist.e1 a) -> hsame (outX n) (BHist.e1 a') ->
                  hsame (outY n) (BHist.e1 b) -> hsame (outY n) (BHist.e1 b') ->
                    hsame a b' ∧ hsame a' b := by
  intro sameX sameY classified prefUnary tailUnary prefSame tailSame prefCont outXCont
    prefYCont outYCont outXOne outXOne' outYOne outYOne'
  have tails := RealStreamClassifier_transported_contextual_e1_tail_determinacy
    sameX sameY classified prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont
    outYCont outXOne outXOne' outYOne outYOne'
  have sameAA' : hsame a a' := tails.right.right.right.right.left
  have sameBB' : hsame b b' := tails.right.right.right.right.right.left
  have sameAB : hsame a b := tails.right.right.right.right.right.right.left
  exact And.intro (hsame_trans sameAB sameBB') (hsame_trans (hsame_symm sameAA') sameAB)

end BEDC.Derived.RealUp
