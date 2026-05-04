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
  intro classified prefXUnary tailXUnary prefSame tailSame prefXCont outXCont prefYCont
    outYCont n
  have contextClassifier :
      RatHistoryClassifier (append (pX n) (append (x n) (tX n)))
        (append (pY n) (append (y n) (tY n))) :=
    RatHistoryClassifier_unary_denominator_context_closed (classified n)
      (prefXUnary n) (prefSame n) (tailXUnary n) (tailSame n)
  have sameOutX : hsame (append (pX n) (append (x n) (tX n))) (oX n) := by
    have prefEq : mX n = append (pX n) (x n) := cont_iff_append.mp (prefXCont n)
    have outEq : oX n = append (mX n) (tX n) := cont_iff_append.mp (outXCont n)
    exact (append_assoc (pX n) (x n) (tX n)).symm.trans
      ((congrArg (fun h => append h (tX n)) prefEq).symm.trans outEq.symm)
  have sameOutY : hsame (append (pY n) (append (y n) (tY n))) (oY n) := by
    have prefEq : mY n = append (pY n) (y n) := cont_iff_append.mp (prefYCont n)
    have outEq : oY n = append (mY n) (tY n) := cont_iff_append.mp (outYCont n)
    exact (append_assoc (pY n) (y n) (tY n)).symm.trans
      ((congrArg (fun h => append h (tY n)) prefEq).symm.trans outEq.symm)
  exact RatHistoryClassifier_hsame_transport sameOutX sameOutY contextClassifier

theorem RealConstantHistoryClassifier_append_common_tail_cancel {d e tail : BHist} :
    RealConstantHistoryClassifier (BHist.e1 (append d tail)) (BHist.e1 (append e tail)) ->
      hsame d e := by
  intro classified
  have rational :
      RatHistoryClassifier (append d tail) (append e tail) :=
    Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
  exact append_right_cancel (k := tail) rational.right.right

theorem RealStreamClassifier_unary_denominator_context_selected_e1_pair_readback
    {x y pX pY tX tY mX mY oX oY : Nat -> BHist} {n : Nat} {a b : BHist} :
    RealStreamClassifier x y ->
      (forall i : Nat, UnaryHistory (pX i)) ->
        (forall i : Nat, UnaryHistory (tX i)) ->
          (forall i : Nat, hsame (pX i) (pY i)) ->
            (forall i : Nat, hsame (tX i) (tY i)) ->
              (forall i : Nat, Cont (pX i) (x i) (mX i)) ->
                (forall i : Nat, Cont (mX i) (tX i) (oX i)) ->
                  (forall i : Nat, Cont (pY i) (y i) (mY i)) ->
                    (forall i : Nat, Cont (mY i) (tY i) (oY i)) ->
                      hsame (oX n) (BHist.e1 a) -> hsame (oY n) (BHist.e1 b) ->
                        UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified prefixX tailX samePrefix sameTail contPX contOX contPY contOY sameLeft
    sameRight
  have contextClassified : RealStreamClassifier oX oY :=
    RealStreamClassifier_unary_denominator_context_closed classified prefixX tailX samePrefix
      sameTail contPX contOX contPY contOY
  exact RealStreamClassifier_selected_e1_pair_readback contextClassified sameLeft sameRight

theorem RealStreamClassifier_unary_context_closed
    {x y prefX prefY tailX tailY : Nat -> BHist} :
    (forall i : Nat, UnaryHistory (prefX i)) ->
      (forall i : Nat, hsame (prefX i) (prefY i)) ->
        (forall i : Nat, UnaryHistory (tailX i)) ->
          (forall i : Nat, hsame (tailX i) (tailY i)) ->
            RealStreamClassifier x y ->
              RealStreamClassifier
                (fun i => append (prefX i) (append (x i) (tailX i)))
                (fun i => append (prefY i) (append (y i) (tailY i))) := by
  intro prefUnary prefSame tailUnary tailSame classified i
  exact RatHistoryClassifier_unary_denominator_context_closed (classified i)
    (prefUnary i) (prefSame i) (tailUnary i) (tailSame i)

end BEDC.Derived.RealUp
