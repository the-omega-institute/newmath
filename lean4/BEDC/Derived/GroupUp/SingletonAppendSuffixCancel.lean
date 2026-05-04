import BEDC.Derived.GroupUp.SingletonContext
import BEDC.Derived.GroupUp.SingletonContinuation

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

theorem GroupSingletonClassifier_append_suffix_unit_split_iff {L R p q : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      (GroupSingletonClassifier (append (append p q) L) (append BHist.Empty R) <->
        GroupSingletonCarrier p ∧ GroupSingletonCarrier q) := by
  intro carrierL carrierR
  exact Iff.trans
    (GroupSingletonClassifier_append_suffix_cancel_iff (P := append p q) (R := L)
      (Q := BHist.Empty) (S := R) carrierL carrierR)
    GroupSingletonClassifier_append_unit_split_iff

theorem GroupSingletonClassifier_two_sided_contextual_coverage_iff {L R L' R' Q S : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      GroupSingletonCarrier L' -> GroupSingletonCarrier R' ->
        (GroupSingletonClassifier (append (append L Q) L') (append (append R S) R') <->
          GroupSingletonCarrier Q ∧ GroupSingletonCarrier S) := by
  intro carrierL carrierR carrierL' carrierR'
  exact Iff.trans
    (GroupSingletonClassifier_right_context_cancel_iff (L := L') (R := R')
      (Q := append L Q) (S := append R S) carrierL' carrierR')
      (Iff.trans
        (GroupSingletonClassifier_append_context_cancel_iff (L := L) (R := R)
          (Q := Q) (S := S) carrierL carrierR)
        (GroupSingleton_terminal_classifier_package.left Q S))

theorem GroupSingletonClassifier_two_sided_contextual_carrier_coverage_iff
    {L R Lp Rp Q S : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R -> GroupSingletonCarrier Lp ->
      GroupSingletonCarrier Rp ->
      (GroupSingletonClassifier (append (append L Q) Lp) (append (append R S) Rp) <->
        GroupSingletonCarrier Q ∧ GroupSingletonCarrier S) := by
  intro carrierL carrierR carrierLp carrierRp
  have suffixCancel :=
    GroupSingletonClassifier_append_suffix_cancel_iff (P := append L Q) (R := Lp)
      (Q := append R S) (S := Rp) carrierLp carrierRp
  have prefixCancel :=
    GroupSingletonClassifier_append_context_cancel_iff (L := L) (R := R)
      (Q := Q) (S := S) carrierL carrierR
  exact Iff.trans suffixCancel
    (Iff.trans prefixCancel (GroupSingleton_terminal_classifier_package.left Q S))

theorem GroupSingletonClassifier_two_sided_contextual_continuation_product_unit_coverage_iff
    {L0 R0 L1 R1 P Q S T : BHist} :
    GroupSingletonCarrier L0 -> GroupSingletonCarrier R0 ->
      GroupSingletonCarrier L1 -> GroupSingletonCarrier R1 -> Cont P Q S ->
        (GroupSingletonClassifier (append (append L0 (append S T)) L1)
          (append (append R0 BHist.Empty) R1) <->
            GroupSingletonCarrier P ∧ GroupSingletonCarrier Q ∧ GroupSingletonCarrier T) := by
  intro carrierL0 carrierR0 carrierL1 carrierR1 continuation
  have contextualIff :=
    GroupSingletonClassifier_two_sided_contextual_coverage_iff (L := L0) (R := R0)
      (L' := L1) (R' := R1) (Q := append S T) (S := BHist.Empty)
      carrierL0 carrierR0 carrierL1 carrierR1
  have splitIff := GroupSingleton_terminal_classifier_package.right.left S T
  have continuationIff := GroupSingletonClassifier_continuation_result_carrier_iff continuation
  have terminalIff := GroupSingleton_terminal_classifier_package.left P Q
  constructor
  · intro classified
    have contextual := contextualIff.mp classified
    have split := splitIff.mp contextual.left
    have classifiedPQ : GroupSingletonClassifier P Q := continuationIff.mpr split.left
    have carriersPQ := terminalIff.mp classifiedPQ
    exact And.intro carriersPQ.left (And.intro carriersPQ.right split.right)
  · intro carriers
    have classifiedPQ : GroupSingletonClassifier P Q :=
      terminalIff.mpr (And.intro carriers.left carriers.right.left)
    have carrierS : GroupSingletonCarrier S := continuationIff.mp classifiedPQ
    have carrierST : GroupSingletonCarrier (append S T) :=
      splitIff.mpr (And.intro carrierS carriers.right.right)
    exact contextualIff.mpr (And.intro carrierST (hsame_refl BHist.Empty))

end BEDC.Derived.GroupUp
