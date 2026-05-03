import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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
