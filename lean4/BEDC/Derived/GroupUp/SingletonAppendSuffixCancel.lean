import BEDC.Derived.GroupUp.SingletonContext

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

theorem GroupSingleton_terminal_classifier_package :
    (forall h k : BHist, GroupSingletonClassifier h k <->
      GroupSingletonCarrier h /\ GroupSingletonCarrier k) /\
      (forall p q : BHist, GroupSingletonCarrier (append p q) <->
        GroupSingletonCarrier p /\ GroupSingletonCarrier q) /\
      (forall h : BHist, GroupSingletonCarrier h ->
        GroupSingletonCarrier BHist.Empty /\
          GroupSingletonClassifier BHist.Empty h /\
            GroupSingletonClassifier h BHist.Empty) := by
  constructor
  · intro h k
    constructor
    · intro classified
      exact And.intro classified.left classified.right.left
    · intro carriers
      exact And.intro carriers.left
        (And.intro carriers.right (hsame_trans carriers.left (hsame_symm carriers.right)))
  · constructor
    · intro p q
      constructor
      · intro carrier
        exact append_eq_empty_iff.mp carrier
      · intro carriers
        exact append_eq_empty_iff.mpr carriers
    · intro h carrier
      have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
      constructor
      · exact emptyCarrier
      · constructor
        · exact And.intro emptyCarrier (And.intro carrier (hsame_symm carrier))
        · exact And.intro carrier (And.intro emptyCarrier carrier)

theorem GroupSingletonClassifier_suffix_context_product_unit_split_iff {L R p q : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      (GroupSingletonClassifier (append (append p q) L) (append BHist.Empty R) <->
        GroupSingletonCarrier p /\ GroupSingletonCarrier q) := by
  intro carrierL carrierR
  have cancel :=
    GroupSingletonClassifier_right_context_cancel_iff (L := L) (R := R) (Q := append p q)
      (S := BHist.Empty) carrierL carrierR
  constructor
  · intro classified
    exact GroupSingletonClassifier_append_unit_split_iff.mp (cancel.mp classified)
  · intro carriers
    exact cancel.mpr (GroupSingletonClassifier_append_unit_split_iff.mpr carriers)

end BEDC.Derived.GroupUp
