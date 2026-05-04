import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonCarrier_append_context_empty_iff {L R h : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      (GroupSingletonCarrier (append L (append h R)) <-> GroupSingletonCarrier h) := by
  intro carrierL carrierR
  constructor
  · intro contextualCarrier
    have outerSplit := append_eq_empty_iff.mp contextualCarrier
    exact (append_eq_empty_iff.mp outerSplit.right).left
  · intro carrierH
    exact append_eq_empty_iff.mpr
      (And.intro carrierL (append_eq_empty_iff.mpr (And.intro carrierH carrierR)))

theorem GroupSingletonClassifier_append_product_empty_split_iff {a b c d : BHist} :
    GroupSingletonClassifier (append a b) (append c d) ↔
      GroupSingletonCarrier a ∧ GroupSingletonCarrier b ∧
        GroupSingletonCarrier c ∧ GroupSingletonCarrier d := by
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.left
      (And.intro leftSplit.right (And.intro rightSplit.left rightSplit.right))
  · intro split
    have leftCarrier : GroupSingletonCarrier (append a b) :=
      append_eq_empty_iff.mpr (And.intro split.left split.right.left)
    have rightCarrier : GroupSingletonCarrier (append c d) :=
      append_eq_empty_iff.mpr (And.intro split.right.right.left split.right.right.right)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.GroupUp
