import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonCarrier_hsame_empty_transport_iff {h k : BHist} (sameHK : hsame h k) :
    FieldSingletonCarrier h ↔ hsame k BHist.Empty := by
  constructor
  · intro carrierH
    exact hsame_trans (hsame_symm sameHK) carrierH
  · intro carrierK
    exact hsame_trans sameHK carrierK

theorem FieldSingletonClassifier_hsame_empty_transport_iff {h h' k k' : BHist}
    (sameH : hsame h h') (sameK : hsame k k') :
    FieldSingletonClassifier h' k' ↔
      hsame h BHist.Empty ∧ hsame k BHist.Empty ∧ hsame h k := by
  constructor
  · intro classified
    exact And.intro (hsame_trans sameH classified.left)
      (And.intro (hsame_trans sameK classified.right.left)
        (hsame_trans sameH (hsame_trans classified.right.right (hsame_symm sameK))))
  · intro data
    exact And.intro (hsame_trans (hsame_symm sameH) data.left)
      (And.intro (hsame_trans (hsame_symm sameK) data.right.left)
        (hsame_trans (hsame_symm sameH) (hsame_trans data.right.right sameK)))

theorem FieldSingletonClassifier_continuation_left_endpoint_transport_iff {P Q R S : BHist} :
    FieldSingletonCarrier Q -> Cont P Q R ->
      (FieldSingletonClassifier R S <-> FieldSingletonClassifier P S) := by
  intro carrierQ continuation
  cases carrierQ
  have sameRP : hsame R P := cont_deterministic continuation (cont_right_unit P)
  constructor
  · intro classified
    exact And.intro (hsame_trans (hsame_symm sameRP) classified.left)
      (And.intro classified.right.left
        (hsame_trans (hsame_symm sameRP) classified.right.right))
  · intro classified
    exact And.intro (hsame_trans sameRP classified.left)
      (And.intro classified.right.left (hsame_trans sameRP classified.right.right))

theorem FieldSingletonClassifier_continuation_right_endpoint_transport_iff {P Q R S : BHist} :
    FieldSingletonCarrier P -> Cont P Q R ->
      (FieldSingletonClassifier R S <-> FieldSingletonClassifier Q S) := by
  intro carrierP continuation
  cases carrierP
  have sameRQ : hsame R Q := cont_left_unit_result continuation
  constructor
  · intro classified
    exact And.intro (hsame_trans (hsame_symm sameRQ) classified.left)
      (And.intro classified.right.left
        (hsame_trans (hsame_symm sameRQ) classified.right.right))
  · intro classified
    exact And.intro (hsame_trans sameRQ classified.left)
      (And.intro classified.right.left (hsame_trans sameRQ classified.right.right))

end BEDC.Derived.FieldUp
