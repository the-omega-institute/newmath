import BEDC.Derived.GroupUp.SingletonAppendSuffixCancel
import BEDC.Derived.GroupUp.SingletonContinuation

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_two_sided_contextual_continuation_product_unit_coverage_iff
    {L0 R0 L1 R1 P Q S T : BHist} :
    GroupSingletonCarrier L0 -> GroupSingletonCarrier R0 -> GroupSingletonCarrier L1 ->
      GroupSingletonCarrier R1 -> Cont P Q S ->
      (GroupSingletonClassifier (append (append L0 (append S T)) L1)
          (append (append R0 BHist.Empty) R1) <->
        GroupSingletonCarrier P ∧ GroupSingletonCarrier Q ∧ GroupSingletonCarrier T) := by
  intro carrierL0 carrierR0 carrierL1 carrierR1 continuation
  have contextual :=
    GroupSingletonClassifier_two_sided_contextual_coverage_iff (L := L0) (R := R0)
      (L' := L1) (R' := R1) (Q := append S T) (S := BHist.Empty)
      carrierL0 carrierR0 carrierL1 carrierR1
  constructor
  · intro classified
    have splitContext := contextual.mp classified
    have splitProduct := append_eq_empty_iff.mp splitContext.left
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation splitProduct.left
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro endpoints.left (And.intro endpoints.right splitProduct.right)
  · intro carriers
    have resultCarrier : GroupSingletonCarrier S :=
      cont_respects_hsame carriers.left carriers.right.left continuation
        (cont_right_unit BHist.Empty)
    have productCarrier : GroupSingletonCarrier (append S T) :=
      append_eq_empty_iff.mpr (And.intro resultCarrier carriers.right.right)
    exact contextual.mpr (And.intro productCarrier (hsame_refl BHist.Empty))

theorem GroupSingletonClassifier_two_sided_contextual_continuation_product_unit_visible_absurd
    {L0 R0 L1 R1 P Q S T r : BHist} :
    GroupSingletonCarrier L0 -> GroupSingletonCarrier R0 -> GroupSingletonCarrier L1 ->
      GroupSingletonCarrier R1 -> Cont P Q S ->
      GroupSingletonClassifier (append (append L0 (append S T)) L1)
        (append (append R0 BHist.Empty) R1) ->
      (Cont P Q (BHist.e0 r) -> False) ∧ (Cont P Q (BHist.e1 r) -> False) := by
  intro carrierL0 carrierR0 carrierL1 carrierR1 continuation classified
  have coverage :=
    GroupSingletonClassifier_two_sided_contextual_continuation_product_unit_coverage_iff
      (L0 := L0) (R0 := R0) (L1 := L1) (R1 := R1) (P := P) (Q := Q)
      (S := S) (T := T) carrierL0 carrierR0 carrierL1 carrierR1 continuation
  have carriers := coverage.mp classified
  have classifiedPQ : GroupSingletonClassifier P Q :=
    And.intro carriers.left
      (And.intro carriers.right.left
        (hsame_trans carriers.left (hsame_symm carriers.right.left)))
  exact GroupSingletonClassifier_continuation_visible_result_absurd classifiedPQ

theorem GroupSingletonClassifier_continuation_product_unit_coverage_iff {P Q S T : BHist} :
    Cont P Q S ->
      (GroupSingletonClassifier (append S T) BHist.Empty <->
        GroupSingletonCarrier P ∧ GroupSingletonCarrier Q ∧ GroupSingletonCarrier T) := by
  intro continuation
  constructor
  · intro classified
    have split := GroupSingletonClassifier_append_unit_split_iff.mp classified
    have inputClassified :=
      (GroupSingletonClassifier_continuation_result_carrier_iff continuation).mpr split.left
    exact And.intro inputClassified.left
      (And.intro inputClassified.right.left split.right)
  · intro carriers
    have inputClassified : GroupSingletonClassifier P Q :=
      And.intro carriers.left
        (And.intro carriers.right.left
          (hsame_trans carriers.left (hsame_symm carriers.right.left)))
    have resultCarrier :=
      (GroupSingletonClassifier_continuation_result_carrier_iff continuation).mp inputClassified
    exact GroupSingletonClassifier_append_unit_split_iff.mpr
      (And.intro resultCarrier carriers.right.right)

end BEDC.Derived.GroupUp
