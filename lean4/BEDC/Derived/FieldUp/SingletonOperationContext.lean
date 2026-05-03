import BEDC.Derived.FieldUp
import BEDC.Derived.FieldUp.SingletonAppend
import BEDC.Derived.FieldUp.SingletonEmpty
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem fieldSingletonEmptyClassifier_append_endpoint_iff {L R endpoint out : BHist}
    (hL : fieldSingletonEmptyCarrier L) (hR : fieldSingletonEmptyCarrier R)
    (hEndpoint : fieldSingletonEmptyCarrier endpoint) :
    fieldSingletonEmptyClassifier (append L endpoint) (append R out) ↔
      fieldSingletonEmptyCarrier out := by
  constructor
  · intro classified
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact rightSplit.right
  · intro outCarrier
    have leftCarrier : fieldSingletonEmptyCarrier (append L endpoint) :=
      append_eq_empty_iff.mpr (And.intro hL hEndpoint)
    have rightCarrier : fieldSingletonEmptyCarrier (append R out) :=
      append_eq_empty_iff.mpr (And.intro hR outCarrier)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem fieldSingletonEmpty_operation_context_normalization {L R h k out : BHist}
    (hL : fieldSingletonEmptyCarrier L) (hR : fieldSingletonEmptyCarrier R) :
    (fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyMul h k)) (append R out) ↔
      fieldSingletonEmptyCarrier out) ∧
    (fieldSingletonEmptyClassifier (append L fieldSingletonEmptyOne) (append R out) ↔
      fieldSingletonEmptyCarrier out) ∧
    (∀ (p : fieldSingletonEmptyNonZero h),
      fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyInv h p)) (append R out) ↔
        fieldSingletonEmptyCarrier out) := by
  constructor
  · exact fieldSingletonEmptyClassifier_append_endpoint_iff hL hR (hsame_refl BHist.Empty)
  · constructor
    · exact fieldSingletonEmptyClassifier_append_endpoint_iff hL hR (hsame_refl BHist.Empty)
    · intro p
      exact fieldSingletonEmptyClassifier_append_endpoint_iff hL hR (hsame_refl BHist.Empty)

theorem fieldSingletonEmpty_operation_context_nonzero_obstruction {L R h k out : BHist}
    (carrierL : fieldSingletonEmptyCarrier L) (carrierR : fieldSingletonEmptyCarrier R)
    (nonzeroOut : fieldSingletonEmptyNonZero out) :
    (fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyMul h k)) (append R out) ->
      False) ∧
    (fieldSingletonEmptyClassifier (append L fieldSingletonEmptyOne) (append R out) -> False) ∧
    (∀ p : fieldSingletonEmptyNonZero h,
      fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyInv h p)) (append R out) ->
        False) := by
  have normalized :=
    fieldSingletonEmpty_operation_context_normalization (h := h) (k := k) (out := out)
      carrierL carrierR
  constructor
  · intro classified
    exact fieldSingletonEmptyNonZero_empty_endpoint_absurd
      (Iff.mp normalized.left classified) nonzeroOut
  · constructor
    · intro classified
      exact fieldSingletonEmptyNonZero_empty_endpoint_absurd
        (Iff.mp normalized.right.left classified) nonzeroOut
    · intro p classified
      exact fieldSingletonEmptyNonZero_empty_endpoint_absurd
        (Iff.mp (normalized.right.right p) classified) nonzeroOut

theorem fieldSingletonEmpty_operation_context_carried_nonzero_obstruction
    {L R U V h k out : BHist}
    (carrierL : fieldSingletonEmptyCarrier L) (carrierR : fieldSingletonEmptyCarrier R)
    (carrierU : fieldSingletonEmptyCarrier U) (carrierV : fieldSingletonEmptyCarrier V)
    (carriedNonzero : fieldSingletonEmptyNonZero (append U (append out V))) :
    (fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyMul h k)) (append R out) ->
      False) ∧
    (fieldSingletonEmptyClassifier (append L fieldSingletonEmptyOne) (append R out) -> False) ∧
    (∀ p : fieldSingletonEmptyNonZero h,
      fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyInv h p)) (append R out) ->
        False) := by
  have nonzeroOut : fieldSingletonEmptyNonZero out :=
    Iff.mp (fieldSingletonEmptyNonZero_append_context_cancel_iff carrierU carrierV)
      carriedNonzero
  exact fieldSingletonEmpty_operation_context_nonzero_obstruction carrierL carrierR nonzeroOut

theorem FieldSingletonClassifier_operation_context_endpoint_package {L R h k out : BHist}
    (carrierL : FieldSingletonCarrier L) (carrierR : FieldSingletonCarrier R) :
    (FieldSingletonClassifier (append L (FieldSingletonMul h k)) (append R out) ↔
      FieldSingletonCarrier out) ∧
    (FieldSingletonClassifier (append L FieldSingletonOne) (append R out) ↔
      FieldSingletonCarrier out) ∧
    (∀ p : FieldSingletonNonZero h,
      FieldSingletonClassifier (append L (FieldSingletonInv h p)) (append R out) ↔
        FieldSingletonCarrier out) := by
  have endpointIff : ∀ endpoint : BHist, FieldSingletonCarrier endpoint ->
      (FieldSingletonClassifier (append L endpoint) (append R out) ↔
        FieldSingletonCarrier out) := by
    intro endpoint endpointCarrier
    constructor
    · intro classified
      exact (append_eq_empty_iff.mp classified.right.left).right
    · intro outCarrier
      have leftCarrier : FieldSingletonCarrier (append L endpoint) :=
        append_eq_empty_iff.mpr (And.intro carrierL endpointCarrier)
      have rightCarrier : FieldSingletonCarrier (append R out) :=
        append_eq_empty_iff.mpr (And.intro carrierR outCarrier)
      exact And.intro leftCarrier
        (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
  constructor
  · exact endpointIff (FieldSingletonMul h k) (hsame_refl BHist.Empty)
  · constructor
    · exact endpointIff FieldSingletonOne (hsame_refl BHist.Empty)
    · intro p
      exact endpointIff (FieldSingletonInv h p) (hsame_refl BHist.Empty)

theorem FieldSingletonAddNegZero_operation_context_endpoint_package {L R h k out : BHist}
    (carrierL : FieldSingletonCarrier L) (carrierR : FieldSingletonCarrier R) :
    (FieldSingletonClassifier (append L (FieldSingletonAdd h k)) (append R out) ↔
      FieldSingletonCarrier out) ∧
    (FieldSingletonClassifier (append L (FieldSingletonNeg h)) (append R out) ↔
      FieldSingletonCarrier out) ∧
    (FieldSingletonClassifier (append L FieldSingletonZero) (append R out) ↔
      FieldSingletonCarrier out) := by
  have endpointIff : ∀ endpoint : BHist, FieldSingletonCarrier endpoint ->
      (FieldSingletonClassifier (append L endpoint) (append R out) ↔
        FieldSingletonCarrier out) := by
    intro endpoint endpointCarrier
    constructor
    · intro classified
      exact (append_eq_empty_iff.mp classified.right.left).right
    · intro outCarrier
      have leftCarrier : FieldSingletonCarrier (append L endpoint) :=
        append_eq_empty_iff.mpr (And.intro carrierL endpointCarrier)
      have rightCarrier : FieldSingletonCarrier (append R out) :=
        append_eq_empty_iff.mpr (And.intro carrierR outCarrier)
      exact And.intro leftCarrier
        (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
  constructor
  · exact endpointIff (FieldSingletonAdd h k) (hsame_refl BHist.Empty)
  · constructor
    · exact endpointIff (FieldSingletonNeg h) (hsame_refl BHist.Empty)
    · exact endpointIff FieldSingletonZero (hsame_refl BHist.Empty)

end BEDC.Derived.FieldUp
