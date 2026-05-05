import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamPrefixClassifier_truncated_e1_pair_readback {x y : Nat -> BHist} :
    forall {n m : Nat} {leftTail rightTail : BHist},
      RealStreamPrefixClassifier x y (m + n) ->
        hsame (x n) (BHist.e1 leftTail) ->
          hsame (y n) (BHist.e1 rightTail) ->
            UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
  intro n m
  induction m with
  | zero =>
      intro leftTail rightTail classified sameLeft sameRight
      simp only [Nat.zero_add] at classified
      exact RealStreamPrefixClassifier_e1_pair_readback classified sameLeft sameRight
  | succ m ih =>
      intro leftTail rightTail classified sameLeft sameRight
      have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
        simp only [Nat.succ_add] at classified
        exact classified
      exact ih stepClassified.left sameLeft sameRight

theorem RealStreamPrefixClassifier_truncated_endpoint_denominator_package
    {x y : Nat -> BHist} {m n : Nat} :
    RealStreamPrefixClassifier x y (m + n) ->
      RatHistoryClassifier (x n) (y n) ∧
        PositiveUnaryDenominator (x n) ∧
          PositiveUnaryDenominator (y n) ∧
            UnaryHistory (x n) ∧
              UnaryHistory (y n) ∧
                (hsame (x n) BHist.Empty -> False) ∧
                  (hsame (y n) BHist.Empty -> False) := by
  intro classified
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have endpointClassified : RatHistoryClassifier (x n) (y n) :=
    RealStreamPrefixClassifier_endpoint n prefixAtN
  have positiveRows :
      PositiveUnaryDenominator (x n) ∧ PositiveUnaryDenominator (y n) :=
    RatHistoryClassifier_positive_denominators endpointClassified
  have leftRows : UnaryHistory (x n) ∧ (hsame (x n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.left
  have rightRows : UnaryHistory (y n) ∧ (hsame (y n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.right
  exact And.intro endpointClassified
    (And.intro positiveRows.left
      (And.intro positiveRows.right
        (And.intro leftRows.left
          (And.intro rightRows.left (And.intro leftRows.right rightRows.right)))))

theorem RealStreamPrefixClassifier_truncated_endpoint_common_e1_tail_readback
    {x y : Nat -> BHist} {m n : Nat} :
    RealStreamPrefixClassifier x y (m + n) ->
      exists a b : BHist, hsame (x n) (BHist.e1 a) ∧ hsame (y n) (BHist.e1 b) ∧
        UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified
  have package :=
    RealStreamPrefixClassifier_truncated_endpoint_denominator_package classified
  have leftShape :=
    unary_history_nonempty_e1_tail package.right.right.right.left
      package.right.right.right.right.right.left
  have rightShape :=
    unary_history_nonempty_e1_tail package.right.right.right.right.left
      package.right.right.right.right.right.right
  cases leftShape with
  | intro a aShape =>
      cases rightShape with
      | intro b bShape =>
          have tails :=
            RealStreamPrefixClassifier_truncated_e1_pair_readback classified aShape.left
              bShape.left
          exact Exists.intro a
            (Exists.intro b
              (And.intro aShape.left
                (And.intro bShape.left
                  (And.intro tails.left (And.intro tails.right.left tails.right.right)))))

theorem RealStreamPrefixClassifier_truncated_cont_endpoint_context_closed
    {x y prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {m n : Nat} :
    RealStreamPrefixClassifier x y (m + n) -> UnaryHistory (prefX n) ->
      UnaryHistory (tailX n) -> hsame (prefX n) (prefY n) ->
        hsame (tailX n) (tailY n) -> Cont (prefX n) (x n) (midX n) ->
          Cont (midX n) (tailX n) (outX n) -> Cont (prefY n) (y n) (midY n) ->
            Cont (midY n) (tailY n) (outY n) ->
              RatHistoryClassifier (outX n) (outY n) := by
  intro classified prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont
    outYCont
  have prefixAtN : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  have endpointClassified : RatHistoryClassifier (x n) (y n) :=
    RealStreamPrefixClassifier_endpoint n prefixAtN
  have contextClassified :
      RatHistoryClassifier
        (append (prefX n) (append (x n) (tailX n)))
        (append (prefY n) (append (y n) (tailY n))) :=
    RatHistoryClassifier_unary_denominator_context_closed endpointClassified prefUnary prefSame
      tailUnary tailSame
  have sameOutX : hsame (append (prefX n) (append (x n) (tailX n))) (outX n) := by
    have outEq : outX n = append (append (prefX n) (x n)) (tailX n) :=
      Eq.trans outXCont (congrArg (fun z => append z (tailX n)) prefCont)
    exact hsame_trans (hsame_symm (append_assoc (prefX n) (x n) (tailX n))) outEq.symm
  have sameOutY : hsame (append (prefY n) (append (y n) (tailY n))) (outY n) := by
    have outEq : outY n = append (append (prefY n) (y n)) (tailY n) :=
      Eq.trans outYCont (congrArg (fun z => append z (tailY n)) prefYCont)
    exact hsame_trans (hsame_symm (append_assoc (prefY n) (y n) (tailY n))) outEq.symm
  exact RatHistoryClassifier_hsame_transport sameOutX sameOutY contextClassified

theorem RealStreamPrefixClassifier_contextual_e1_denominator_package
    {x y prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {m n : Nat}
    {leftTail rightTail : BHist} :
    RealStreamPrefixClassifier x y (m + n) -> UnaryHistory (prefX n) ->
      UnaryHistory (tailX n) -> hsame (prefX n) (prefY n) ->
        hsame (tailX n) (tailY n) -> Cont (prefX n) (x n) (midX n) ->
          Cont (midX n) (tailX n) (outX n) -> Cont (prefY n) (y n) (midY n) ->
            Cont (midY n) (tailY n) (outY n) ->
              RatHistoryClassifier (outX n) (outY n) ∧
                PositiveUnaryDenominator (outX n) ∧ PositiveUnaryDenominator (outY n) ∧
                  UnaryHistory (outX n) ∧ UnaryHistory (outY n) ∧
                    (hsame (outX n) BHist.Empty -> False) ∧
                      (hsame (outY n) BHist.Empty -> False) ∧
                        (hsame (outX n) (BHist.e1 leftTail) ->
                          hsame (outY n) (BHist.e1 rightTail) ->
                            UnaryHistory leftTail ∧ UnaryHistory rightTail ∧
                              hsame leftTail rightTail) := by
  intro classified prefUnary tailUnary prefSame tailSame prefXCont outXCont prefYCont
    outYCont
  have contextClassified :
      RatHistoryClassifier (outX n) (outY n) :=
    RealStreamPrefixClassifier_truncated_cont_endpoint_context_closed classified prefUnary
      tailUnary prefSame tailSame prefXCont outXCont prefYCont outYCont
  have positives :
      PositiveUnaryDenominator (outX n) ∧ PositiveUnaryDenominator (outY n) :=
    RatHistoryClassifier_positive_denominators contextClassified
  have leftRows : UnaryHistory (outX n) ∧ (hsame (outX n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows : UnaryHistory (outY n) ∧ (hsame (outY n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  have tailReadback :
      hsame (outX n) (BHist.e1 leftTail) ->
        hsame (outY n) (BHist.e1 rightTail) ->
          UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
    intro sameLeft sameRight
    have displayed :
        RatHistoryClassifier (BHist.e1 leftTail) (BHist.e1 rightTail) :=
      RatHistoryClassifier_hsame_transport sameLeft sameRight contextClassified
    exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  exact And.intro contextClassified
    (And.intro positives.left
      (And.intro positives.right
        (And.intro leftRows.left
          (And.intro rightRows.left
            (And.intro leftRows.right
              (And.intro rightRows.right tailReadback))))))

theorem RealStreamPrefixClassifier_contextual_e0_endpoint_absurd
    {x y prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {m n : Nat}
    {zX zY : BHist} :
    RealStreamPrefixClassifier x y (m + n) -> UnaryHistory (prefX n) ->
      UnaryHistory (tailX n) -> hsame (prefX n) (prefY n) ->
        hsame (tailX n) (tailY n) -> Cont (prefX n) (x n) (midX n) ->
          Cont (midX n) (tailX n) (outX n) -> Cont (prefY n) (y n) (midY n) ->
            Cont (midY n) (tailY n) (outY n) ->
              (hsame (outX n) (BHist.e0 zX) -> False) ∧
                (hsame (outY n) (BHist.e0 zY) -> False) := by
  intro classified prefUnary tailUnary prefSame tailSame prefCont outXCont prefYCont
    outYCont
  have package := RealStreamPrefixClassifier_contextual_e1_denominator_package
    (leftTail := zX) (rightTail := zY) classified prefUnary tailUnary prefSame tailSame
    prefCont outXCont prefYCont outYCont
  exact ⟨fun sameZero => PositiveUnaryDenominator_e0_absurd
    (PositiveUnaryDenominator_hsame_transport sameZero package.right.left),
    fun sameZero => PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameZero package.right.right.left)⟩

theorem RealStreamPrefixClassifier_contextual_full_endpoint_package
    {x y prefX prefY tailX tailY midX midY outX outY : Nat -> BHist} {m n : Nat}
    {leftTail rightTail zX zY : BHist} :
    RealStreamPrefixClassifier x y (m + n) -> UnaryHistory (prefX n) ->
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
  have e1Package := RealStreamPrefixClassifier_contextual_e1_denominator_package
    (leftTail := leftTail) (rightTail := rightTail) classified prefUnary tailUnary prefSame
    tailSame prefCont outXCont prefYCont outYCont
  have e0Absurd := RealStreamPrefixClassifier_contextual_e0_endpoint_absurd
    (zX := zX) (zY := zY) classified prefUnary tailUnary prefSame tailSame prefCont
    outXCont prefYCont outYCont
  have tailPackage : UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail :=
    e1Package.right.right.right.right.right.right.right outXOne outYOne
  exact And.intro e1Package.left
    (And.intro e1Package.right.left
      (And.intro e1Package.right.right.left
        (And.intro e1Package.right.right.right.left
          (And.intro e1Package.right.right.right.right.left
            (And.intro e1Package.right.right.right.right.right.left
              (And.intro e1Package.right.right.right.right.right.right.left
                (And.intro e0Absurd.left
                  (And.intro e0Absurd.right tailPackage))))))))

end BEDC.Derived.RealUp
