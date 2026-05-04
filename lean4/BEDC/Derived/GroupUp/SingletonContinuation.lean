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

theorem GroupSingletonCarrier_continuation_endpoint_split_iff {P Q R : BHist} :
    Cont P Q R -> (GroupSingletonCarrier R <-> GroupSingletonCarrier P /\ GroupSingletonCarrier Q) := by
  intro continuation
  constructor
  · intro carrierR
    exact cont_empty_result_inversion (cont_result_hsame_transport continuation carrierR)
  · intro endpoints
    exact cont_respects_hsame endpoints.left endpoints.right continuation
      (cont_right_unit BHist.Empty)

theorem GroupSingletonCarrier_inverse_continuation_roundtrip_iff {x r s : BHist} :
    Cont (GroupSingletonInv x) x r ->
      Cont r (GroupSingletonInv x) s ->
        (GroupSingletonCarrier s <-> GroupSingletonCarrier x) := by
  intro firstContinuation secondContinuation
  have firstIff := GroupSingletonInv_continuation_left_unit_iff firstContinuation
  have secondIff := GroupSingletonCarrier_continuation_endpoint_split_iff secondContinuation
  constructor
  · intro carrierS
    have split := secondIff.mp carrierS
    have classifiedR : GroupSingletonClassifier r BHist.Empty :=
      And.intro split.left
        (And.intro (hsame_refl BHist.Empty) split.left)
    exact firstIff.mp classifiedR
  · intro carrierX
    have classifiedR : GroupSingletonClassifier r BHist.Empty :=
      firstIff.mpr carrierX
    have inverseCarrier : GroupSingletonCarrier (GroupSingletonInv x) :=
      hsame_refl BHist.Empty
    exact secondIff.mpr (And.intro classifiedR.left inverseCarrier)

theorem GroupSingletonClassifier_inverse_continuation_roundtrip_source_iff {x r s : BHist} :
    Cont (GroupSingletonInv x) x r ->
      Cont r (GroupSingletonInv x) s ->
        (GroupSingletonClassifier s x <-> GroupSingletonCarrier x) := by
  intro firstContinuation secondContinuation
  have roundtrip :=
    GroupSingletonCarrier_inverse_continuation_roundtrip_iff firstContinuation secondContinuation
  constructor
  · intro classified
    exact classified.right.left
  · intro carrierX
    have carrierS := roundtrip.mpr carrierX
    exact And.intro carrierS
      (And.intro carrierX (hsame_trans carrierS (hsame_symm carrierX)))

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

theorem GroupSingletonClassifier_continuation_terminal_collapse {P Q R r : BHist} :
    Cont P Q R ->
      (GroupSingletonClassifier P Q <-> GroupSingletonClassifier R P) ∧
        (GroupSingletonClassifier P Q <-> GroupSingletonClassifier R Q) ∧
          (GroupSingletonClassifier P Q <-> GroupSingletonCarrier R) ∧
            (GroupSingletonClassifier P Q ->
              (Cont P Q (BHist.e0 r) -> False) ∧ (Cont P Q (BHist.e1 r) -> False)) := by
  intro continuation
  exact And.intro (GroupSingletonClassifier_continuation_result_left_iff continuation)
    (And.intro (GroupSingletonClassifier_continuation_result_right_iff continuation)
      (And.intro (GroupSingletonClassifier_continuation_result_carrier_iff continuation)
        (fun classified =>
          GroupSingletonClassifier_continuation_visible_result_absurd classified)))

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
