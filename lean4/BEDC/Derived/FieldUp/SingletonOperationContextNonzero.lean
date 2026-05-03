import BEDC.Derived.FieldUp.SingletonEmpty

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem fieldSingletonEmpty_operation_context_nonzero_absurd {L R h k out : BHist}
    (carrierL : fieldSingletonEmptyCarrier L) (carrierR : fieldSingletonEmptyCarrier R)
    (nonzeroOut : fieldSingletonEmptyNonZero out) :
    (fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyMul h k)) (append R out) ->
        False) ∧
      (fieldSingletonEmptyClassifier (append L fieldSingletonEmptyOne) (append R out) ->
        False) ∧
        (∀ p : fieldSingletonEmptyNonZero h,
          fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyInv h p)) (append R out) ->
            False) := by
  have norm := fieldSingletonEmptyClassifier_operation_context_normalization
    (h := h) (k := k) (out := out) carrierL carrierR
  constructor
  · intro classified
    exact fieldSingletonEmptyNonZero_empty_endpoint_absurd (Iff.mp norm.left classified)
      nonzeroOut
  · constructor
    · intro classified
      exact fieldSingletonEmptyNonZero_empty_endpoint_absurd (Iff.mp norm.right.left classified)
        nonzeroOut
    · intro p classified
      exact fieldSingletonEmptyNonZero_empty_endpoint_absurd
        (Iff.mp (norm.right.right p) classified) nonzeroOut

end BEDC.Derived.FieldUp
