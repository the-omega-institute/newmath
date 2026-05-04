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

end BEDC.Derived.RealUp
