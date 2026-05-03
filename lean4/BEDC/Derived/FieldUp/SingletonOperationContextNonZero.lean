import BEDC.Derived.FieldUp.SingletonAppend
import BEDC.Derived.FieldUp.SingletonOperationContext

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem fieldSingletonEmptyClassifier_operation_context_nonzero_absurd {L R h k out : BHist}
    (hL : fieldSingletonEmptyCarrier L) (hR : fieldSingletonEmptyCarrier R)
    (nonzeroOut : fieldSingletonEmptyNonZero out) :
    (fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyMul h k)) (append R out) -> False) ∧
    (fieldSingletonEmptyClassifier (append L fieldSingletonEmptyOne) (append R out) -> False) ∧
    (∀ (p : fieldSingletonEmptyNonZero h),
      fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyInv h p)) (append R out) -> False) := by
  have normalized :=
    fieldSingletonEmpty_operation_context_normalization (L := L) (R := R) (h := h) (k := k)
      (out := out) hL hR
  constructor
  · intro classified
    have outCarrier : fieldSingletonEmptyCarrier out := Iff.mp normalized.left classified
    exact fieldSingletonEmptyNonZero_empty_endpoint_absurd outCarrier nonzeroOut
  · constructor
    · intro classified
      have outCarrier : fieldSingletonEmptyCarrier out := Iff.mp normalized.right.left classified
      exact fieldSingletonEmptyNonZero_empty_endpoint_absurd outCarrier nonzeroOut
    · intro p classified
      have outCarrier : fieldSingletonEmptyCarrier out := Iff.mp (normalized.right.right p) classified
      exact fieldSingletonEmptyNonZero_empty_endpoint_absurd outCarrier nonzeroOut

theorem fieldSingletonEmptyClassifier_operation_context_carried_nonzero_absurd {L R U V h k out : BHist}
    (hL : fieldSingletonEmptyCarrier L) (hR : fieldSingletonEmptyCarrier R)
    (hU : fieldSingletonEmptyCarrier U) (hV : fieldSingletonEmptyCarrier V)
    (nonzeroCarried : fieldSingletonEmptyNonZero (append U (append out V))) :
    (fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyMul h k)) (append R out) -> False) ∧
    (fieldSingletonEmptyClassifier (append L fieldSingletonEmptyOne) (append R out) -> False) ∧
    (∀ (p : fieldSingletonEmptyNonZero h),
      fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyInv h p)) (append R out) -> False) := by
  have nonzeroOut : fieldSingletonEmptyNonZero out :=
    Iff.mp (fieldSingletonEmptyNonZero_append_context_cancel_iff hU hV) nonzeroCarried
  exact fieldSingletonEmptyClassifier_operation_context_nonzero_absurd hL hR nonzeroOut

end BEDC.Derived.FieldUp
