import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_append_suffix_cancel_iff {P R Q S : BHist} :
    GroupSingletonCarrier R -> GroupSingletonCarrier S ->
      (GroupSingletonClassifier (append P R) (append Q S) <-> GroupSingletonClassifier P Q) := by
  intro carrierR carrierS
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.left
      (And.intro rightSplit.left (hsame_trans leftSplit.left (hsame_symm rightSplit.left)))
  · intro classified
    have leftCarrier : GroupSingletonCarrier (append P R) :=
      append_eq_empty_iff.mpr (And.intro classified.left carrierR)
    have rightCarrier : GroupSingletonCarrier (append Q S) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierS)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.GroupUp
