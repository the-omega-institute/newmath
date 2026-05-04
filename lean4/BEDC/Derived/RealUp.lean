import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.StreamNameUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.RealUp.PrefixTruncation
import BEDC.Derived.RealUp.ConstantStreamBridge
import BEDC.Derived.RealUp.ConstantStream
import BEDC.Derived.RealUp.StreamReadback
import BEDC.Derived.RealUp.Readback

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_unary_denominator_context_closed
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} :
    RealStreamClassifier x y ->
      (forall n : Nat, UnaryHistory (pX n)) ->
        (forall n : Nat, UnaryHistory (tX n)) ->
          (forall n : Nat, hsame (pX n) (pY n)) ->
            (forall n : Nat, hsame (tX n) (tY n)) ->
              (forall n : Nat, Cont (pX n) (x n) (mX n)) ->
                (forall n : Nat, Cont (mX n) (tX n) (oX n)) ->
                  (forall n : Nat, Cont (pY n) (y n) (mY n)) ->
                    (forall n : Nat, Cont (mY n) (tY n) (oY n)) ->
                      RealStreamClassifier oX oY := by
  intro classified prefixX tailX samePrefix sameTail contPX contOX contPY contOY n
  have pointContext :
      RatHistoryClassifier (append (pX n) (append (x n) (tX n)))
        (append (pY n) (append (y n) (tY n))) :=
    RatHistoryClassifier_unary_denominator_context_closed (classified n) (prefixX n)
      (samePrefix n) (tailX n) (sameTail n)
  have sameOutX : hsame (append (pX n) (append (x n) (tX n))) (oX n) := by
    exact (append_assoc (pX n) (x n) (tX n)).symm.trans
      ((contOX n).trans (congrArg (fun r => append r (tX n)) (contPX n))).symm
  have sameOutY : hsame (append (pY n) (append (y n) (tY n))) (oY n) := by
    exact (append_assoc (pY n) (y n) (tY n)).symm.trans
      ((contOY n).trans (congrArg (fun r => append r (tY n)) (contPY n))).symm
  exact RatHistoryClassifier_hsame_transport sameOutX sameOutY pointContext

theorem RealStreamPrefixClassifier_truncated_unary_context_closed
    {x y prefX prefY tailX tailY : Nat -> BHist} :
    (forall i : Nat, UnaryHistory (prefX i)) ->
      (forall i : Nat, hsame (prefX i) (prefY i)) ->
        (forall i : Nat, UnaryHistory (tailX i)) ->
          (forall i : Nat, hsame (tailX i) (tailY i)) ->
            forall {n m : Nat}, RealStreamPrefixClassifier x y (m + n) ->
              RealStreamPrefixClassifier
                (fun i => append (prefX i) (append (x i) (tailX i)))
                (fun i => append (prefY i) (append (y i) (tailY i))) n := by
  intro prefUnary prefSame tailUnary tailSame n m classified
  have truncated : RealStreamPrefixClassifier x y n := by
    induction m with
    | zero =>
        simp only [Nat.zero_add] at classified
        exact classified
    | succ m ih =>
        have stepClassified : RealStreamPrefixClassifier x y (Nat.succ (m + n)) := by
          simp only [Nat.succ_add] at classified
          exact classified
        exact ih stepClassified.left
  exact RealStreamPrefixClassifier_unary_context_closed prefUnary prefSame tailUnary tailSame n
    truncated

end BEDC.Derived.RealUp
