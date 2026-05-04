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

end BEDC.Derived.RealUp
