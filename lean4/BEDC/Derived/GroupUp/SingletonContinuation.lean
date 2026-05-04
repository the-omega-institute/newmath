import BEDC.Derived.GroupUp.SingletonContext

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_continuation_visible_result_absurd {P Q r : BHist} :
    GroupSingletonClassifier P Q ->
      (Cont P Q (BHist.e0 r) -> False) ∧ (Cont P Q (BHist.e1 r) -> False) := by
  intro classified
  constructor
  · intro continuation
    have resultEmpty : hsame (BHist.e0 r) BHist.Empty :=
      cont_respects_hsame classified.left classified.right.left continuation
        (cont_right_unit BHist.Empty)
    exact not_hsame_e0_empty resultEmpty
  · intro continuation
    have resultEmpty : hsame (BHist.e1 r) BHist.Empty :=
      cont_respects_hsame classified.left classified.right.left continuation
        (cont_right_unit BHist.Empty)
    exact not_hsame_e1_empty resultEmpty

theorem GroupSingletonClassifier_continuation_result_left_iff {P Q R : BHist} :
    Cont P Q R -> (GroupSingletonClassifier P Q <-> GroupSingletonClassifier R P) := by
  intro continuation
  constructor
  · intro classified
    have resultCarrier : GroupSingletonCarrier R :=
      cont_respects_hsame classified.left classified.right.left continuation
        (cont_right_unit BHist.Empty)
    exact And.intro resultCarrier
      (And.intro classified.left (hsame_trans resultCarrier (hsame_symm classified.left)))
  · intro resultClassified
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation resultClassified.left
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

theorem GroupSingletonInv_continuation_left_unit_iff {x r : BHist} :
    Cont (GroupSingletonInv x) x r ->
      (GroupSingletonClassifier r BHist.Empty <-> GroupSingletonCarrier x) := by
  intro continuation
  cases continuation
  constructor
  · intro classified
    exact (append_eq_empty_iff.mp classified.left).right
  · intro carrierX
    have resultCarrier : GroupSingletonCarrier (append (GroupSingletonInv x) x) :=
      append_eq_empty_iff.mpr (And.intro (hsame_refl BHist.Empty) carrierX)
    exact And.intro resultCarrier
      (And.intro (hsame_refl BHist.Empty) resultCarrier)

theorem GroupSingletonClassifier_continuation_result_right_iff {P Q R : BHist} :
    Cont P Q R -> (GroupSingletonClassifier P Q <-> GroupSingletonClassifier R Q) := by
  intro continuation
  constructor
  · intro classified
    have resultCarrier : GroupSingletonCarrier R :=
      cont_respects_hsame classified.left classified.right.left continuation
        (cont_right_unit BHist.Empty)
    exact And.intro resultCarrier
      (And.intro classified.right.left
        (hsame_trans resultCarrier (hsame_symm classified.right.left)))
  · intro resultClassified
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation resultClassified.left
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

theorem GroupSingletonClassifier_continuation_result_carrier_iff {P Q R : BHist} :
    Cont P Q R -> (GroupSingletonClassifier P Q <-> GroupSingletonCarrier R) := by
  intro continuation
  constructor
  · intro classified
    exact cont_respects_hsame classified.left classified.right.left continuation
      (cont_right_unit BHist.Empty)
  · intro resultCarrier
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation resultCarrier
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

theorem GroupSingletonClassifier_continuation_endpoint_equivalence_iff {P Q R : BHist} :
    Cont P Q R -> (GroupSingletonClassifier R P <-> GroupSingletonClassifier R Q) := by
  intro continuation
  have leftIff := GroupSingletonClassifier_continuation_result_left_iff continuation
  have rightIff := GroupSingletonClassifier_continuation_result_right_iff continuation
  constructor
  · intro classifiedRP
    exact rightIff.mp (leftIff.mpr classifiedRP)
  · intro classifiedRQ
    exact leftIff.mp (rightIff.mpr classifiedRQ)

theorem GroupSingletonClassifier_contextual_continuation_endpoint_equivalence_iff
    {L R L' R' P Q S : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R -> GroupSingletonCarrier L' ->
      GroupSingletonCarrier R' -> Cont P Q S ->
        (GroupSingletonClassifier (append (append L S) L') (append (append R P) R') <->
          GroupSingletonClassifier (append (append L S) L') (append (append R Q) R')) := by
  intro carrierL carrierR carrierL' carrierR' continuation
  have suffixLeft :=
    GroupSingletonClassifier_right_context_cancel_iff (L := L') (R := R')
      (Q := append L S) (S := append R P) carrierL' carrierR'
  have suffixRight :=
    GroupSingletonClassifier_right_context_cancel_iff (L := L') (R := R')
      (Q := append L S) (S := append R Q) carrierL' carrierR'
  have prefixLeft :=
    GroupSingletonClassifier_append_context_cancel_iff (L := L) (R := R)
      (Q := S) (S := P) carrierL carrierR
  have prefixRight :=
    GroupSingletonClassifier_append_context_cancel_iff (L := L) (R := R)
      (Q := S) (S := Q) carrierL carrierR
  have endpoint :=
    GroupSingletonClassifier_continuation_endpoint_equivalence_iff continuation
  constructor
  · intro classified
    exact suffixRight.mpr (prefixRight.mpr (endpoint.mp (prefixLeft.mp (suffixLeft.mp classified))))
  · intro classified
    exact suffixLeft.mpr (prefixLeft.mpr (endpoint.mpr (prefixRight.mp (suffixRight.mp classified))))

end BEDC.Derived.GroupUp
