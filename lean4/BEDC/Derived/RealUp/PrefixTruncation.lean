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

end BEDC.Derived.RealUp
