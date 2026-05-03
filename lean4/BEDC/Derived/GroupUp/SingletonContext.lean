import BEDC.Derived.GroupUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_right_context_cancel_iff {L R Q S : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      (GroupSingletonClassifier (append Q L) (append S R) <-> GroupSingletonClassifier Q S) := by
  intro carrierL carrierR
  have sameSuffix : hsame L R := hsame_trans carrierL (hsame_symm carrierR)
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    have sameQS : hsame Q S :=
      Iff.mp
        (append_hsame_right_context_cancel_iff (P := L) (Q := R) (a := Q) (b := S)
          sameSuffix)
        classified.right.right
    exact And.intro leftSplit.left (And.intro rightSplit.left sameQS)
  · intro classified
    have leftCarrier : GroupSingletonCarrier (append Q L) :=
      append_eq_empty_iff.mpr (And.intro classified.left carrierL)
    have rightCarrier : GroupSingletonCarrier (append S R) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierR)
    have sameAppend : hsame (append Q L) (append S R) :=
      Iff.mpr
        (append_hsame_right_context_cancel_iff (P := L) (Q := R) (a := Q) (b := S)
          sameSuffix)
        classified.right.right
    exact And.intro leftCarrier (And.intro rightCarrier sameAppend)

theorem GroupSingletonCarrier_append_visible_head_absurd {p q : BHist} :
    (GroupSingletonCarrier (append (BHist.e0 p) q) -> False) ∧
      (GroupSingletonCarrier (append (BHist.e1 p) q) -> False) := by
  constructor
  · intro carrier
    exact not_hsame_e0_empty (append_eq_empty_iff.mp carrier).left
  · intro carrier
    exact not_hsame_e1_empty (append_eq_empty_iff.mp carrier).left

end BEDC.Derived.GroupUp
